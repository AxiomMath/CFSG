module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport

public section

namespace CFSG.QuasithinUnique.Ch1.SporAut

open CFSG.ComponentClassification.OuterAutomorphisms

theorem cocycle_coboundary_of_coprime {L A : Type*} [Group L] [CommGroup A] [Finite L] [Finite A]
    (ρ : L →* MulAut A) (S : Subgroup L) (hcop : Nat.Coprime (Nat.card A) S.index)
    (d : L → A) (hd : ∀ x y, d (x * y) = d x * ρ x (d y)) (hS : ∀ x, ∀ s ∈ S, d (x * s) = d x) :
    ∃ b : A, ∀ x, d x = b * (ρ x b)⁻¹ := by
  classical
  have : Fintype (L ⧸ S) := Fintype.ofFinite _
  let D : L ⧸ S → A := Quotient.lift d (fun x y hxy => by
    have h : x⁻¹ * y ∈ S := QuotientGroup.leftRel_apply.1 hxy
    have := hS x _ h
    simpa using this.symm)
  have hD : ∀ x (c : L ⧸ S), D (x • c) = d x * ρ x (D c) := by
    intro x c
    induction c using Quotient.inductionOn with
    | _ y => exact hd x y
  let b : A := ∏ c : L ⧸ S, D c
  have hb : ∀ x, d x ^ S.index = b * (ρ x b)⁻¹ := by
    intro x
    have h1 : ∏ c : L ⧸ S, D (x • c) = b :=
      Equiv.prod_comp (MulAction.toPerm x) D
    have h2 : ∏ c : L ⧸ S, D (x • c) = d x ^ S.index * ρ x b := by
      simp only [hD, Finset.prod_mul_distrib, Finset.prod_const]
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index,
        ← map_prod (ρ x) D Finset.univ]
    rw [h2] at h1
    rw [eq_mul_inv_iff_mul_eq]
    exact h1
  let e : A ≃ A := powCoprime hcop
  have he : ∀ a, e a = a ^ S.index := fun a => rfl
  have h3 : (e.symm b) ^ S.index = b := by
    rw [← he]
    exact e.apply_symm_apply b
  refine ⟨e.symm b, fun x => ?_⟩
  apply e.injective
  have key : (e.symm b * (ρ x (e.symm b))⁻¹) ^ S.index = b * (ρ x b)⁻¹ := by
    rw [mul_pow, inv_pow, ← map_pow (ρ x) (e.symm b) S.index, h3]
  rw [he, he, hb x, key]

open scoped IsMulCommutative in
theorem exists_conj_of_fixing_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (L Q S : Subgroup G) (hQS : Q ≤ S) (hQp : IsPGroup p Q)
    (hQL : ∀ x ∈ L, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hC : L ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hidx : ¬ p ∣ S.relIndex L)
    (α : MulAut G) (hαL : ∀ x ∈ L, α x ∈ L) (hαS : ∀ s ∈ S, α s = s) :
    ∃ c ∈ Q, (∀ q ∈ Q, c * q = q * c) ∧ ∀ x ∈ L, α x = c * x * c⁻¹ := by
  classical
  set A : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G) with hA
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext
    ((Subgroup.mem_centralizer_iff.1 a.2.2 b b.2.1).symm)⟩⟩
  have hLA : ∀ x ∈ L, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx a ha
    refine ⟨hQL x hx a ha.1, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have h1 : x⁻¹ * q * x ∈ Q := by
      simpa using hQL x⁻¹ (L.inv_mem hx) q hq
    have h2 := Subgroup.mem_centralizer_iff.1 ha.2 _ h1
    calc q * (x * a * x⁻¹) = x * ((x⁻¹ * q * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * q * x)) * x⁻¹ := by rw [h2]
      _ = x * a * x⁻¹ * q := by group
  have hLN : L ≤ (Subgroup.normalizer (A : Set G)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hLA x hx a ha, fun ha => by
      have := hLA x⁻¹ (L.inv_mem hx) _ ha
      simpa [mul_assoc] using this⟩
  let ρ : L →* MulAut A := (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hLN)
  have hρ : ∀ (x : L) (a : A), ((ρ x a : A) : G) = x * a * (x : G)⁻¹ := fun x a => rfl
  have hdA : ∀ x ∈ L, α x * x⁻¹ ∈ A := by
    intro x hx
    have hxL : α x * x⁻¹ ∈ L := L.mul_mem (hαL x hx) (L.inv_mem hx)
    have hcent : α x * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : x⁻¹ * q * x ∈ Q := by simpa using hQL x⁻¹ (L.inv_mem hx) q hq
      have h2 := hαS _ (hQS h1)
      rw [map_mul, map_mul, map_inv, hαS q (hQS hq)] at h2
      have h2' : (α x)⁻¹ * q * α x = x⁻¹ * q * x := h2
      calc q * (α x * x⁻¹) = α x * ((α x)⁻¹ * q * α x) * x⁻¹ := by group
        _ = α x * (x⁻¹ * q * x) * x⁻¹ := by rw [h2']
        _ = α x * x⁻¹ * q := by group
    exact ⟨hC ⟨hxL, hcent⟩, hcent⟩
  let d : L → A := fun x => ⟨α x * (x : G)⁻¹, hdA x x.2⟩
  have hd : ∀ x y, d (x * y) = d x * ρ x (d y) := by
    intro x y
    apply Subtype.ext
    change α ((x : G) * y) * ((x : G) * y)⁻¹ =
      (α x * (x : G)⁻¹) * ((x : G) * (α y * (y : G)⁻¹) * (x : G)⁻¹)
    rw [map_mul]
    group
  have hS' : ∀ x, ∀ s ∈ S.subgroupOf L, d (x * s) = d x := by
    intro x s hs
    apply Subtype.ext
    have hsS : (s : G) ∈ S := hs
    change α ((x : G) * s) * ((x : G) * s)⁻¹ = α x * (x : G)⁻¹
    rw [map_mul, hαS _ hsS]
    group
  have hAp : IsPGroup p A := IsPGroup.to_le hQp (inf_le_left : A ≤ Q)
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (S.subgroupOf L).index := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hidx)
  obtain ⟨b, hb⟩ := cocycle_coboundary_of_coprime ρ (S.subgroupOf L) hcop d hd hS'
  refine ⟨b, b.2.1, fun q hq => (Subgroup.mem_centralizer_iff.1 b.2.2 q hq).symm, fun x hx => ?_⟩
  have h := congrArg (fun a : A => (a : G)) (hb ⟨x, hx⟩)
  simp only [d, Subgroup.coe_mul, Subgroup.coe_inv, hρ] at h
  calc α x = (α x * x⁻¹) * x := by group
    _ = (b : G) * (x * (b : G) * x⁻¹)⁻¹ * x := by rw [h]
    _ = (b : G) * x * (b : G)⁻¹ := by group

theorem exists_conj_of_local_pair {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G)
    (hH : H = Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G))
    (K : Subgroup G) (hKS : K ≤ S) (N : Subgroup G) (hN : N = Subgroup.normalizer (K : Set G))
    (J : Subgroup G) (hJp : IsPGroup p J) (hJS : J ≤ S) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hCJ : H ⊓ Subgroup.centralizer (J : Set G) ≤ J)
    (hCK : N ⊓ Subgroup.centralizer (K : Set G) ≤ K) (hgen : H ⊔ N = ⊤)
    (hSN : (S : Subgroup G) ≤ N)
    (α : MulAut G) (hα : ∀ s ∈ (S : Subgroup G), α s = s) :
    ∃ c : G, ∀ x, α x = c * x * c⁻¹ := by
  classical
  set Z : Subgroup G := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  have hZS : ∀ z ∈ Z, α z = z := by
    rintro z ⟨y, -, rfl⟩
    exact hα y y.2
  have hmemZ : ∀ c ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * c = c * s) → c ∈ Z := by
    intro c hc hcs
    refine ⟨⟨c, hc⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcs g g.2), rfl⟩
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro z ⟨y, hy, rfl⟩
    have := Subgroup.mem_center_iff.1 hy ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hSdiv : ∀ L : Subgroup G, (S : Subgroup G) ≤ L → ¬ p ∣ (S : Subgroup G).relIndex L := by
    intro L hL hdvd
    exact S.not_dvd_index (dvd_trans hdvd (Subgroup.relIndex_dvd_index_of_le hL))
  have hαH : ∀ x ∈ H, α x ∈ H := by
    intro x hx
    rw [hH, Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have := hx z hz
    rw [← hZS z hz, ← map_mul, ← map_mul, this]
  have hαK : ∀ k ∈ K, α k = k := fun k hk => hα k (hKS hk)
  have hαKs : ∀ k ∈ K, α.symm k = k := fun k hk => by
    have := congrArg α.symm (hαK k hk)
    simpa using this.symm
  have hαN : ∀ x ∈ N, α x ∈ N := by
    intro x hx
    rw [hN, Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    have e : α x * h * (α x)⁻¹ = α (x * α.symm h * x⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [e]
    constructor
    · intro hh
      rw [hαKs h hh]
      have h2 := (hx h).1 hh
      rw [hαK _ h2]
      exact h2
    · intro hh
      have h3 : x * α.symm h * x⁻¹ ∈ K := by
        have h4 : α (x * α.symm h * x⁻¹) = α (α (x * α.symm h * x⁻¹)) := by
          rw [hαK _ hh]
        rw [α.injective h4]
        exact hh
      have h5 : α.symm h ∈ K := (hx _).2 h3
      have h6 : h = α.symm h := by
        have := hαK _ h5
        rwa [MulEquiv.apply_symm_apply] at this
      rw [h6]
      exact h5
  have hQH : ∀ x ∈ H, ∀ q ∈ J, x * q * x⁻¹ ∈ J := fun x hx q hq =>
    (Subgroup.normal_subgroupOf_iff hJH).1 hJn q x hq hx
  obtain ⟨c1, hc1J, -, hc1⟩ := exists_conj_of_fixing_sylow H J S hJS hJp hQH hCJ
    (hSdiv H hSH) α hαH hα
  have hc1Z : c1 ∈ Z := hmemZ c1 (hJS hc1J) fun s hs => by
    have h := hc1 s (hSH hs)
    rw [hα s hs] at h
    calc s * c1 = c1 * s * c1⁻¹ * c1 := by rw [← h]
      _ = c1 * s := by group
  have hHc : ∀ z ∈ Z, ∀ x ∈ H, z * x = x * z := by
    intro z hz x hx
    rw [hH, Subgroup.mem_centralizer_iff] at hx
    exact hx z hz
  have hαHid : ∀ x ∈ H, α x = x := by
    intro x hx
    rw [hc1 x hx]
    have := hHc c1 hc1Z x hx
    calc c1 * x * c1⁻¹ = x * c1 * c1⁻¹ := by rw [this]
      _ = x := by group
  have hKN : ∀ x ∈ N, ∀ q ∈ K, x * q * x⁻¹ ∈ K := by
    intro x hx q hq
    rw [hN, Subgroup.mem_normalizer_iff] at hx
    exact (hx q).1 hq
  obtain ⟨c2, hc2K, -, hc2⟩ := exists_conj_of_fixing_sylow N K S hKS
    (IsPGroup.to_le S.isPGroup' hKS) hKN hCK (hSdiv N hSN) α hαN hα
  have hc2Z : c2 ∈ Z := hmemZ c2 (hKS hc2K) fun s hs => by
    have h := hc2 s (hSN hs)
    rw [hα s hs] at h
    calc s * c2 = c2 * s * c2⁻¹ * c2 := by rw [← h]
      _ = c2 * s := by group
  refine ⟨c2, fun x => ?_⟩
  have hle : H ⊔ N ≤ MonoidHom.eqLocus (α : G →* G) (MulAut.conj c2 : G →* G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · change α y = c2 * y * c2⁻¹
      rw [hαHid y hy]
      have := hHc c2 hc2Z y hy
      calc y = y * c2 * c2⁻¹ := by group
        _ = c2 * y * c2⁻¹ := by rw [this]
    · exact hc2 y hy
  exact hle (by rw [hgen]; trivial)

open scoped Pointwise in
theorem exists_conj_of_sylow_fixing {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (S₀ P' : Sylow p N)
    (h : ∀ α : MulAut N, (∀ s ∈ (S₀ : Subgroup N), α s = s) → ∃ c : N, ∀ x, α x = c * x * c⁻¹)
    (α : MulAut N) (hα : ∀ s ∈ (P' : Subgroup N), α s = s) :
    ∃ c : N, ∀ x, α x = c * x * c⁻¹ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P' S₀
  have hmem : ∀ s ∈ (S₀ : Subgroup N), g⁻¹ * s * g ∈ (P' : Subgroup N) := by
    intro s hs
    have hs' : s ∈ MulAut.conj g • (P' : Subgroup N) := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hs
    obtain ⟨t, ht, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs'
    have : g⁻¹ * s * g = t := by
      rw [← hts, MulAut.smul_def, MulAut.conj_apply]
      group
    rw [this]
    exact ht
  have key : ∀ y, (MulAut.conj g * α * (MulAut.conj g)⁻¹) y = g * α (g⁻¹ * y * g) * g⁻¹ := by
    intro y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  obtain ⟨c, hc⟩ := h (MulAut.conj g * α * (MulAut.conj g)⁻¹) (fun s hs => by
    rw [key, hα _ (hmem s hs)]
    group)
  refine ⟨g⁻¹ * c * g, fun x => ?_⟩
  have h3 := hc (g * x * g⁻¹)
  rw [key, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h3
  calc α x = g⁻¹ * (g * α x * g⁻¹) * g := by group
    _ = g⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * g := by rw [h3]
    _ = (g⁻¹ * c * g) * x * (g⁻¹ * c * g)⁻¹ := by group

theorem exists_conj_of_pair {N : Type*} [Group N] (a b : N)
    (hgen : Subgroup.closure ({a, b} : Set N) = ⊤) (α : MulAut N) (ha : α a = a)
    (hb : α b = b ∨ α b = a * b * a⁻¹) : ∃ c : N, ∀ x, α x = c * x * c⁻¹ := by
  rcases hb with hb | hb
  · refine ⟨1, fun x => ?_⟩
    have h : α.toMonoidHom = MonoidHom.id N := by
      refine MonoidHom.eq_of_eqOn_top ?_
      rw [← hgen]
      refine MonoidHom.eqOn_closure ?_
      intro y hy
      rcases hy with h | h
      · rw [h]; exact ha
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact hb
    have := DFunLike.congr_fun h x
    simpa using this
  · refine ⟨a, fun x => ?_⟩
    have h : α.toMonoidHom = (MulAut.conj a).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_top ?_
      rw [← hgen]
      refine MonoidHom.eqOn_closure ?_
      intro y hy
      rcases hy with h | h
      · rw [h]
        change α a = a * a * a⁻¹
        rw [ha]; group
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact hb
    have := DFunLike.congr_fun h x
    simpa using this

theorem eq_or_eq_of_card_two {X : Type*} [Finite X] (h : Nat.card X = 2) (e1 e2 : X)
    (hne : e1 ≠ e2) (z : X) : z = e1 ∨ z = e2 := by
  have : Fintype X := Fintype.ofFinite X
  have hc : Fintype.card X = 2 := by rw [← Nat.card_eq_fintype_card]; exact h
  classical
  have h2 : ({e1, e2} : Finset X).card = 2 := Finset.card_pair hne
  have huniv : ({e1, e2} : Finset X) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [h2, hc])
  have := huniv ▸ Finset.mem_univ z
  simpa using this

theorem isInnerAut_of_fixing_sylow {K : Type} {N : Type*} [Group K] [Group N] [Finite K]
    {p : ℕ} [Fact p.Prime] (ψ : K ≃* N) (S₀ : Sylow p N)
    (h : ∀ α : MulAut N, (∀ s ∈ (S₀ : Subgroup N), α s = s) → ∃ c : N, ∀ x, α x = c * x * c⁻¹)
    (β : K ≃* K) (hP : ∃ P : Sylow p K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  obtain ⟨P, hP⟩ := hP
  have : Finite N := Finite.of_equiv K ψ.toEquiv
  let P' : Sylow p N := P.mapSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hP' : (P' : Subgroup N) = (P : Subgroup K).map ψ.toMonoidHom := rfl
  have hfix : ∀ s ∈ (P' : Subgroup N), transAut ψ β s = s := by
    intro s hs
    rw [hP'] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    change transAut ψ β (ψ t) = ψ t
    rw [transAut_apply, hP t ht]
  obtain ⟨c, hc⟩ := exists_conj_of_sylow_fixing S₀ P' h (transAut ψ β) hfix
  refine isInnerAut_of_transAut_mem_inner ψ β ⟨c, ?_⟩
  ext x
  rw [MulAut.conj_apply]
  exact (hc x).symm

end CFSG.QuasithinUnique.Ch1.SporAut
