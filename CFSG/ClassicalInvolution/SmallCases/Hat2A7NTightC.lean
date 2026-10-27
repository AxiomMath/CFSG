module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NTightB

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Swap

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

theorem TightSettingN.swap_lemma (S : TightSettingN F K z) {u : F} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hE : IsCommProd z u) (hN : u ∈ Subgroup.normalizer (Zset K z))
    (hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x)
    {L : Subgroup F} {v : F} (hL : IsClassical2A7 ⊤ L v) (hLc : IsConjSubgroup K L)
    (hLu : L ≤ Subgroup.centralizer ({u} : Set F)) :
    v = z * (u * z * u⁻¹) ∨ L ≤ Subgroup.centralizer ({z * (u * z * u⁻¹)} : Set F) := by
  have hKz := S.tight.classical
  have hz2 : z * z = 1 := hKz.mul_self
  have hzK : z ∈ K := hKz.mem
  obtain ⟨hbZ', hbz', hzb', he_clos', he1'⟩ := S.swap_data hN hfix
  obtain ⟨b, hb⟩ : ∃ b : F, b = u * z * u⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hbZ' hbz' hzb' he_clos' he1' ⊢
  have hbZ := hbZ'
  have hbz := hbz'
  have hzb := hzb'
  have he_clos := he_clos'
  have he1 := he1'
  have hb2 : b * b = 1 := by
    have : orderOf b = 2 := orderOf_eq_two_of_mem_classOf S.tight hbZ.1
    have h2 := pow_orderOf_eq_one b
    rwa [this, pow_two] at h2
  have hbmemb : memb K z b = K.map (MulAut.conj u).toMonoidHom := by
    rw [hb, memb_conj S.tight (mem_classOf_self z) u, memb_self S.tight]
  have hcoZ : CommOrEq (memb K z z) (memb K z b) := S.commOrEq_of_mem_Zset S.self_mem_Zset hbZ
  have hKcomm : ∀ k ∈ K, ∀ k' ∈ K, k * (u * k' * u⁻¹) = (u * k' * u⁻¹) * k := by
    have hco := hcoZ
    rw [memb_self S.tight, hbmemb] at hco
    rcases hco with h | h
    · exfalso
      apply hbz
      have hbK : b ∈ K := by
        rw [hb]
        have : u * z * u⁻¹ ∈ K.map (MulAut.conj u).toMonoidHom := ⟨z, hzK, rfl⟩
        rwa [← h] at this
      exact hKz.eq_of_orderOf_eq_two hbK (orderOf_eq_two_of_mem_classOf S.tight hbZ.1)
    · intro k hk k' hk'
      exact h k hk _ ⟨k', hk', rfl⟩
  have heord : orderOf (z * b) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; calc z * b * (z * b) = z * (b * z) * b := by group
      _ = z * (z * b) * b := by rw [hzb]
      _ = (z * z) * (b * b) := by group
      _ = 1 := by rw [hz2, hb2]; group) he1
  let φ : ↥K →* F := diagHom K u hKcomm
  let Δ : Subgroup F := φ.range
  have hφz : φ ⟨z, hzK⟩ = z * b := by
    show z * (u * z * u⁻¹) = z * b
    rw [← hb]
  have hΔmem : z * b ∈ Δ := ⟨⟨z, hzK⟩, hφz⟩
  have hKle : K ≤ cliqueSub K z := by
    have := memb_le_cliqueSub (K := K) (z := z) S.self_mem_Zset
    rwa [memb_self S.tight] at this
  have hKule : K.map (MulAut.conj u).toMonoidHom ≤ cliqueSub K z := by
    have := memb_le_cliqueSub (K := K) (z := z) hbZ
    rwa [hbmemb] at this
  have hΔle : Δ ≤ cliqueSub K z := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mul_mem _ (hKle k.2) (hKule ⟨k, k.2, rfl⟩)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hΔcu : ∀ x ∈ Δ, u * x = x * u := by
    rintro _ ⟨k, rfl⟩
    have h1 := hKcomm k k.2 k k.2
    show u * ((k : F) * (u * k * u⁻¹)) = ((k : F) * (u * k * u⁻¹)) * u
    calc u * ((k : F) * (u * k * u⁻¹)) = (u * k * u⁻¹) * (u * (u * k * u⁻¹) * u⁻¹) * u := by group
      _ = (u * k * u⁻¹) * k * u := by
        congr 2
        rw [hui]
        calc u * (u * (k : F) * u) * u = (u * u) * k * (u * u) := by group
          _ = k := by rw [hu2]; group
      _ = ((k : F) * (u * k * u⁻¹)) * u := by rw [← h1]
  have hDVK : cliqueSub K z ≤ Subgroup.normalizer (K : Set F) := by
    have := S.cliqueSub_le_normalizer (S.self_mem_Zset)
    rwa [memb_self S.tight] at this
  set M₁ : Subgroup F := cliqueSub K z ⊓ Subgroup.centralizer ({u} : Set F) with hM₁
  have hΔM₁ : Δ ≤ M₁ := fun x hx =>
    ⟨hΔle hx, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hΔcu x hx⟩
  have hΔnormal : (Δ.subgroupOf M₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔM₁]
    rintro _ d ⟨k, rfl⟩ hd
    have hdK : d ∈ Subgroup.normalizer (K : Set F) := hDVK hd.1
    have hdu : u * d = d * u := Subgroup.mem_centralizer_iff.mp hd.2 u rfl
    have hk2 : d * (k : F) * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK k).mp k.2
    refine ⟨⟨d * (k : F) * d⁻¹, hk2⟩, ?_⟩
    show (d * (k : F) * d⁻¹) * (u * (d * (k : F) * d⁻¹) * u⁻¹) =
      d * ((k : F) * (u * k * u⁻¹)) * d⁻¹
    calc (d * (k : F) * d⁻¹) * (u * (d * (k : F) * d⁻¹) * u⁻¹)
        = d * (k : F) * d⁻¹ * ((u * d) * k * (u * d)⁻¹) := by group
      _ = d * (k : F) * d⁻¹ * ((d * u) * k * (d * u)⁻¹) := by rw [hdu]
      _ = d * ((k : F) * (u * k * u⁻¹)) * d⁻¹ := by group
  have hM₁le : M₁ ≤ Subgroup.centralizer ({u} : Set F) ⊓ Subgroup.centralizer ({z * b} : Set F) :=
    fun x hx => ⟨hx.2, S.cliqueSub_le_centralizer he_clos he1 hx.1⟩
  have hM₁normal : (M₁.subgroupOf (Subgroup.centralizer ({u} : Set F) ⊓
      Subgroup.centralizer ({z * b} : Set F))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM₁le]
    rintro m g hm hg
    have hgN := S.centralizer_le_setNormalizer he_clos he1 hg.2
    have hgu : u * g = g * u := Subgroup.mem_centralizer_iff.mp hg.1 u rfl
    have hmu : u * m = m * u := Subgroup.mem_centralizer_iff.mp hm.2 u rfl
    refine ⟨S.conj_mem_cliqueSub hgN hm.1, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc u * (g * m * g⁻¹) = (u * g) * m * g⁻¹ := by group
      _ = g * (u * m) * g⁻¹ := by rw [hgu]; group
      _ = g * (m * u) * g⁻¹ := by rw [hmu]
      _ = g * m * (u * g⁻¹) := by group
      _ = g * m * (g⁻¹ * u) := by
        congr 1
        calc u * g⁻¹ = g⁻¹ * (g * u) * g⁻¹ := by group
          _ = g⁻¹ * (u * g) * g⁻¹ := by rw [hgu]
          _ = g⁻¹ * u := by group
      _ = g * m * g⁻¹ * u := by group
  have hsubn : IsSubnormal Δ (Subgroup.centralizer ({u} : Set F) ⊓
      Subgroup.centralizer ({z * b} : Set F)) :=
    IsSubnormal.step hΔM₁ hΔnormal (isSubnormal_of_normal_subgroupOf hM₁le hM₁normal)
  have hΔcl : IsClassical2A7 (Subgroup.centralizer ({u} : Set F)) Δ (z * b) := by
    have := hKz.perfect
    refine ⟨heord, hΔmem, Group.IsPerfect.range φ, hsubn, ?_⟩
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
      have hx' : orderOf (((x : ↥K) : ↥K) : F) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hx
      have hxz : (((x : ↥K) : ↥K) : F) = z :=
        hKz.eq_of_orderOf_eq_two (x : ↥K).2 hx'
      have hxker : φ (x : ↥K) = 1 := x.2
      have hxz' : (x : ↥K) = ⟨z, hzK⟩ := Subtype.ext hxz
      rw [hxz', hφz] at hxker
      exact he1 hxker
    exact A7Witness.of_surjective φ.rangeRestrict hsurj hker hKz.witness
  have hMu : IsClassical2A7 (Subgroup.centralizer ({u} : Set F)) L v := hL.mono hLu le_top
  rcases S.IH u (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1) hE Δ L (z * b) v
      (Or.inr ⟨K, IsConjSubgroup.refl K, hKcomm, rfl⟩) hLc hΔcl hMu with h | h
  · left
    have hΔu : z * b ∈ L := by rw [← h]; exact hΔmem
    exact (hL.eq_of_orderOf_eq_two hΔu heord).symm
  · right
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h _ hΔmem c hc

theorem TightSettingN.mem_Zset_of_mem_normalizer (S : TightSettingN F K z) {u : F}
    (hu : u ∈ classOf z) (hN : u ∈ Subgroup.normalizer (Zset K z)) : u ∈ Zset K z := by
  by_contra hnu
  have hTu := S.tight.memb hu
  have hu2 : u * u = 1 := hTu.classical.mul_self
  have hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x := by
    intro x hx hxx
    apply hnu
    refine S.mem_Zset_of_commute_Zset hx hu ?_
    have := congrArg (· * u) hxx
    simpa [mul_assoc] using this
  obtain ⟨hbZ, hbz, hzb, he_clos, he1⟩ := S.swap_data hN hfix
  rcases S.swap_lemma hu2 (S.ne_one hu) (isCommProd_of_mem_classOf hu) hN hfix hTu.classical
      (S.isConjSubgroup_memb hu) hTu.classical.le_centralizer with
    h | h
  ·
    have hcz : u * z = z * u := by
      rw [h]
      calc z * (u * z * u⁻¹) * z = z * ((u * z * u⁻¹) * z) := by group
        _ = z * (z * (u * z * u⁻¹)) := by rw [← hzb]
        _ = z * (z * (u * z * u⁻¹)) := rfl
    apply hbz
    calc u * z * u⁻¹ = z * u * u⁻¹ := by rw [hcz]
      _ = z := by group
  · exact hnu ((S.memb_le_centralizer_iff he_clos he1 hu).mp h)

end Swap

end CFSG.ClassicalInvolution.Hat2A7N
