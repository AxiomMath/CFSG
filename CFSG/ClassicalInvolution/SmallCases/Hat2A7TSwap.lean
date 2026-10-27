module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TStab

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Sub

variable {F : Type} [Group F]

@[expose] def cliqueSub (K : Subgroup F) : Subgroup F := ⨆ N ∈ cliqueSet K, N

theorem le_cliqueSub {K N : Subgroup F} (hN : N ∈ cliqueSet K) : N ≤ cliqueSub K :=
  le_iSup₂ (f := fun (N : Subgroup F) (_ : N ∈ cliqueSet K) => N) N hN

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem cliqueSub_le_normalizer {K N : Subgroup F} (hK : IsMember K) (hN : N ∈ cliqueSet K) :
    cliqueSub K ≤ Subgroup.normalizer (N : Set F) := by
  refine iSup₂_le fun N' hN' => ?_
  have h : CommOrEq N N' := commOrEq_trans hZ IH hN.1 hK hN'.1 hN.2.symm hN'.2
  rcases h with h | h
  · rw [← h]
    exact Subgroup.le_normalizer
  · intro g hg
    have hc : g ∈ Subgroup.centralizer (N : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact h x hx g hg
    exact Subgroup.centralizer_le_normalizer (N : Set F) hc

include hZ IH in
theorem cliqueSub_le_centralizer {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) : cliqueSub K ≤ Subgroup.centralizer ({a} : Set F) :=
  iSup₂_le fun _ hN => le_centralizer_cliqueGrp hZ IH hK hN.1 hN.2 ha

include hZ IH in
theorem map_conj_cliqueSub_le {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {g : F}
    (hg : g ∈ Subgroup.normalizer (cliqueGrp K : Set F)) :
    (cliqueSub K).map (MulAut.conj g).toMonoidHom ≤ cliqueSub K := by
  unfold cliqueSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hN => le_cliqueSub (conj_mem_cliqueSet hZ IH hK hg hN)

end Sub


section Swap

variable {F : Type} [Group F] [Finite F]
variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem mem_normalizer_of_swap {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F}
    (hbH : g * a * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F))
    (hbC : ¬ ∀ x ∈ cliqueGrp K, (g * a * g⁻¹) * x = x * (g * a * g⁻¹)) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hKm : IsMember K := ⟨z, hK⟩
  set b : F := g * a * g⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    have := cliqueGrp_sq hZ IH hKm ha
    calc b * b = g * (a * a) * g⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [this]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, ← hbdef, h]
    group
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  obtain ⟨z₁, hz₁, hmove⟩ : ∃ z₁ ∈ cliqueInv K, b * z₁ ≠ z₁ * b := by
    by_contra hcon
    push Not at hcon
    apply hbC
    have hle : cliqueGrp K ≤ Subgroup.centralizer ({b} : Set F) := by
      refine (Subgroup.closure_le _).mpr fun u hu => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcon u hu).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  obtain ⟨N, hNz, hKN⟩ := hz₁
  have hN : N ∈ cliqueSet K := ⟨⟨z₁, hNz⟩, hKN⟩
  have hz₁A : z₁ ∈ cliqueGrp K := Subgroup.subset_closure ⟨N, hNz, hKN⟩
  set N' : Subgroup F := N.map (MulAut.conj b).toMonoidHom with hN'def
  have hN'mem : N' ∈ cliqueSet K := conj_mem_cliqueSet hZ IH hK hbH hN
  have hN'z : IsClassical2A7 ⊤ N' (b * z₁ * b⁻¹) := by
    have h1 := hNz.conj b
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj b).surjective] at h1
  set z₁' : F := b * z₁ * b⁻¹ with hz₁'def
  have hz₁'N' : z₁' ∈ N' := ⟨z₁, hNz.mem, rfl⟩
  have hz₁'ne : z₁' ≠ z₁ := by
    intro h
    apply hmove
    calc b * z₁ = (b * z₁ * b⁻¹) * b := by group
      _ = z₁ * b := by rw [← hz₁'def, h]
  have hz₁'A : z₁' ∈ cliqueGrp K := (Subgroup.mem_normalizer_iff.mp hbH z₁).mp hz₁A
  have hNN' : N ≠ N' := by
    intro h
    apply hz₁'ne
    exact hNz.eq_of_orderOf_eq_two (h ▸ hz₁'N') hN'z.orderOf_eq_two
  have hcomm : ∀ x ∈ N, ∀ y ∈ N', x * y = y * x := by
    rcases commOrEq_trans hZ IH hN.1 hKm hN'mem.1 hKN.symm hN'mem.2 with h | h
    · exact absurd h hNN'
    · exact h
  have hKc : ∀ k ∈ N, ∀ k' ∈ N, k * (b * k' * b⁻¹) = (b * k' * b⁻¹) * k := fun k hk k' hk' =>
    hcomm k hk _ ⟨k', hk', rfl⟩
  have hz₁z₁' : z₁ * z₁' = z₁' * z₁ := hcomm z₁ hNz.mem z₁' hz₁'N'
  obtain ⟨e, hedef⟩ : ∃ e : F, e = z₁ * z₁' := ⟨_, rfl⟩
  have hee : e * e = 1 := by
    calc e * e = z₁ * (z₁' * z₁) * z₁' := by rw [hedef]; group
      _ = z₁ * (z₁ * z₁') * z₁' := by rw [hz₁z₁']
      _ = (z₁ * z₁) * (z₁' * z₁') := by group
      _ = 1 := by rw [hNz.mul_self, hN'z.mul_self]; group
  have he1 : e ≠ 1 := by
    intro h
    apply hz₁'ne
    rw [hedef] at h
    have h1 : z₁' = z₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hNz.mul_self
  have heo : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hee) he1
  have heA : e ∈ cliqueGrp K := by rw [hedef]; exact Subgroup.mul_mem _ hz₁A hz₁'A
  let φ : ↥N →* F := diagHom N b hKc
  let Δ : Subgroup F := φ.range
  have hφz : φ ⟨z₁, hNz.mem⟩ = e := by rw [hedef]; rfl
  have heΔ : e ∈ Δ := ⟨⟨z₁, hNz.mem⟩, hφz⟩
  have hNE : N ≤ cliqueSub K := le_cliqueSub hN
  have hN'E : N' ≤ cliqueSub K := le_cliqueSub hN'mem
  have hΔE : Δ ≤ cliqueSub K := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mul_mem _ (hNE k.2) (hN'E ⟨k, k.2, rfl⟩)
  have hΔb : ∀ x ∈ Δ, b * x = x * b := by
    rintro _ ⟨k, rfl⟩
    have h1 := hKc k k.2 k k.2
    show b * ((k : F) * (b * k * b⁻¹)) = ((k : F) * (b * k * b⁻¹)) * b
    calc b * ((k : F) * (b * k * b⁻¹)) = (b * k * b⁻¹) * (b * (b * k * b⁻¹) * b⁻¹) * b := by
          group
      _ = (b * k * b⁻¹) * k * b := by
        congr 2
        rw [hbi]
        calc b * (b * (k : F) * b) * b = (b * b) * k * (b * b) := by group
          _ = k := by rw [hb2]; group
      _ = ((k : F) * (b * k * b⁻¹)) * b := by rw [← h1]
  have hEN : cliqueSub K ≤ Subgroup.normalizer (N : Set F) :=
    cliqueSub_le_normalizer hZ IH hKm hN
  set M₁ : Subgroup F := cliqueSub K ⊓ Subgroup.centralizer ({b} : Set F) with hM₁def
  have hΔM₁ : Δ ≤ M₁ := fun x hx =>
    ⟨hΔE hx, Subgroup.mem_centralizer_singleton_iff.mpr (hΔb x hx).symm⟩
  have hΔnormal : (Δ.subgroupOf M₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔM₁]
    rintro _ d ⟨k, rfl⟩ hd
    have hdN : d ∈ Subgroup.normalizer (N : Set F) := hEN hd.1
    have hdb : d * b = b * d := Subgroup.mem_centralizer_singleton_iff.mp hd.2
    have hk2 : d * (k : F) * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hdN k).mp k.2
    refine ⟨⟨d * (k : F) * d⁻¹, hk2⟩, ?_⟩
    show (d * (k : F) * d⁻¹) * (b * (d * (k : F) * d⁻¹) * b⁻¹) =
      d * ((k : F) * (b * k * b⁻¹)) * d⁻¹
    calc (d * (k : F) * d⁻¹) * (b * (d * (k : F) * d⁻¹) * b⁻¹)
        = d * (k : F) * d⁻¹ * ((b * d) * k * (b * d)⁻¹) := by group
      _ = d * (k : F) * d⁻¹ * ((d * b) * k * (d * b)⁻¹) := by rw [hdb]
      _ = d * ((k : F) * (b * k * b⁻¹)) * d⁻¹ := by group
  have hM₁le : M₁ ≤ Subgroup.centralizer ({b} : Set F) ⊓ Subgroup.centralizer ({e} : Set F) :=
    fun x hx => ⟨hx.2, cliqueSub_le_centralizer hZ IH hKm heA hx.1⟩
  have hM₁normal : (M₁.subgroupOf (Subgroup.centralizer ({b} : Set F) ⊓
      Subgroup.centralizer ({e} : Set F))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM₁le]
    rintro m g' hm hg'
    have hg'e : g' * e = e * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'.2
    have hg'H : g' ∈ Subgroup.normalizer (cliqueGrp K : Set F) :=
      centralizer_le_normalizer hZ IH hKm heA he1 hg'e
    have hg'b : g' * b = b * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'.1
    have hmb : m * b = b * m := Subgroup.mem_centralizer_singleton_iff.mp hm.2
    refine ⟨map_conj_cliqueSub_le hZ IH hK hg'H ⟨m, hm.1, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g' * m * g'⁻¹ * b = g' * m * (g'⁻¹ * b) := by group
      _ = g' * m * (b * g'⁻¹) := by
        congr 1
        calc g'⁻¹ * b = g'⁻¹ * (b * g') * g'⁻¹ := by group
          _ = g'⁻¹ * (g' * b) * g'⁻¹ := by rw [hg'b]
          _ = b * g'⁻¹ := by group
      _ = g' * (m * b) * g'⁻¹ := by group
      _ = g' * (b * m) * g'⁻¹ := by rw [hmb]
      _ = b * (g' * m * g'⁻¹) := by
        calc g' * (b * m) * g'⁻¹ = (g' * b) * m * g'⁻¹ := by group
          _ = (b * g') * m * g'⁻¹ := by rw [hg'b]
          _ = b * (g' * m * g'⁻¹) := by group
  have hsubn : IsSubnormal Δ (Subgroup.centralizer ({b} : Set F) ⊓
      Subgroup.centralizer ({e} : Set F)) :=
    IsSubnormal.step hΔM₁ hΔnormal (isSubnormal_of_normal_subgroupOf hM₁le hM₁normal)
  have hΔcl : IsClassical2A7 (Subgroup.centralizer ({b} : Set F)) Δ e := by
    have := hNz.perfect
    refine ⟨heo, heΔ, Group.IsPerfect.range φ, hsubn, ?_⟩
    have hsurj : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
    have hker : Odd (Nat.card φ.rangeRestrict.ker) := by
      rw [MonoidHom.ker_rangeRestrict]
      by_contra hodd
      have hev : 2 ∣ Nat.card φ.ker := by
        rcases Nat.even_or_odd (Nat.card φ.ker) with h | h
        · exact even_iff_two_dvd.mp h
        · exact absurd h hodd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
      have hx' : orderOf (((x : ↥N) : ↥N) : F) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hx
      have hxz : (((x : ↥N) : ↥N) : F) = z₁ := hNz.eq_of_orderOf_eq_two (x : ↥N).2 hx'
      have hxker : φ (x : ↥N) = 1 := x.2
      have hxz' : (x : ↥N) = ⟨z₁, hNz.mem⟩ := Subtype.ext hxz
      rw [hxz', hφz] at hxker
      exact he1 hxker
    exact A7Witness.of_surjective φ.rangeRestrict hsurj hker hNz.witness
  have hKa : K ≤ Subgroup.centralizer ({a} : Set F) :=
    le_centralizer_cliqueGrp hZ IH hKm hKm (CommOrEq.refl K) ha
  have hKg : IsClassical2A7 (Subgroup.centralizer ({b} : Set F)) (K.map (MulAut.conj g).toMonoidHom)
      (g * z * g⁻¹) := by
    have h1 := hK.conj g
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
    exact h1.mono (map_conj_le_centralizer hKa g) le_top
  have hKgm : IsMember (K.map (MulAut.conj g).toMonoidHom) := isMember_map_conj hKm g
  have hKge : K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({e} : Set F) := by
    rcases IH b hbo (centralizer_ne_top_of_orderOf_eq_two hZ hbo) Δ _ e _ hΔcl hKg with h | h
    · rw [← h]
      exact hΔcl.le_centralizer
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h e heΔ k hk).symm
  exact mem_normalizer_of_commOrEq hZ IH hKm
    ((mem_clique_iff_le_centralizer hZ IH hKm hKgm heA he1).mp hKge)

end Swap

end CFSG.ClassicalInvolution.Hat2A7T
