module

public import CFSG.GroupTheory.SteinbergBKFixedPointCoprime
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.GroupTheory.SteinbergBK

open CFSG.Semidihedral.Principal

variable {G : Type*} [Group G]

theorem prime_frobenius_quotient [Finite G] {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) {r : ℕ} (hr : r.Prime) (hR : Nat.card R = r)
    (hfix : ∀ k ∈ K, (∀ x ∈ R, x * k = k * x) → k = 1) (N : Subgroup G) [N.Normal]
    (hNK : N < K) :
    (K.map (QuotientGroup.mk' N)).Normal ∧
      (K.map (QuotientGroup.mk' N)).IsComplement' (R.map (QuotientGroup.mk' N)) ∧
      K.map (QuotientGroup.mk' N) ≠ ⊥ ∧ Nat.card (R.map (QuotientGroup.mk' N)) = r ∧
      (∀ y ∈ K.map (QuotientGroup.mk' N),
        (∀ x ∈ R.map (QuotientGroup.mk' N), x * y = y * x) → y = 1) ∧
      ∀ x ∈ R.map (QuotientGroup.mk' N), x ≠ 1 →
        ∀ y ∈ K.map (QuotientGroup.mk' N), x * y = y * x → y = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hKRd : ∀ x ∈ K, x ∈ R → x = 1 := fun x hxK hxR =>
    Subgroup.disjoint_def.mp hKR.disjoint hxK hxR
  have hcomp : (K.map (QuotientGroup.mk' N)).IsComplement' (R.map (QuotientGroup.mk' N)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      rintro _ ⟨k, hk, rfl⟩ ⟨x, hx, hxk⟩
      have hxk' := hxk
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxk
      have hxK : x ∈ K := by
        have h := mul_mem hk (inv_mem (hNK.le hxk))
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
      rw [← hxk', hKRd x hxK hx, map_one]
    · refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨⟨⟨k, hk⟩, ⟨x, hx⟩⟩, hkx⟩ := hKR.2 g
      refine Set.mem_mul.mpr ⟨_, ⟨k, hk, rfl⟩, _, ⟨x, hx, rfl⟩, ?_⟩
      rw [← map_mul]
      exact congrArg _ hkx
  have hne : K.map (QuotientGroup.mk' N) ≠ ⊥ := by
    obtain ⟨k, hk, hkN⟩ := IsConcreteLE.exists_of_lt hNK
    intro hbot
    have hmem : QuotientGroup.mk' N k ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hkN hmem
  have hcard : Nat.card (R.map (QuotientGroup.mk' N)) = r := by
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp R.subtype) := by
      refine (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext ?_
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact hKRd x (hNK.le hx) x.2
    rw [← Subgroup.range_subtype R, ← MonoidHom.range_comp, ← hR]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  let _ : MulDistribMulAction R K :=
    MulDistribMulAction.compHom K ((MulAut.conjNormal (H := K)).comp R.subtype)
  have hKr : ¬ r ∣ Nat.card K := by
    refine prime_fixed_point_free_coprime hr hR fun k hk => Subtype.ext ?_
    refine hfix k k.2 fun x hx => ?_
    have h : x * k * x⁻¹ = k := by
      have h1 := congrArg Subtype.val (hk ⟨x, hx⟩)
      change ((MulAut.conjNormal x k : K) : G) = k at h1
      rwa [MulAut.conjNormal_apply] at h1
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h]
  have hNr : ¬ r ∣ Nat.card N := fun h => hKr (h.trans (Subgroup.card_dvd_of_le hNK.le))
  have hcent : ∀ y ∈ K.map (QuotientGroup.mk' N),
      (∀ x ∈ R.map (QuotientGroup.mk' N), x * y = y * x) → y = 1 := by
    rintro _ ⟨k, hk, rfl⟩ hy
    let α : R →* MulAut G := MulAut.conj.comp R.subtype
    have hNinv : ∀ a : R, ∀ n ∈ N, α a n ∈ N := fun a n hn =>
      Subgroup.Normal.conj_mem inferInstance n hn a
    have hRp : IsPGroup r R := IsPGroup.of_card (n := 1) (by rw [hR, pow_one])
    have hmem : QuotientGroup.mk' N k ∈
        (QuotientGroup.mk' N) '' {c : G | ∀ a : R, α a c = c} := by
      rw [← coprime_fixed_point_lifting r hRp α N hNinv hNr]
      intro a
      rw [QuotientGroup.mk'_apply, CoprimeFixedPoint.quotientAction_mk]
      have h := hy _ ⟨a, a.2, rfl⟩
      change (((a : G) * k * (a : G)⁻¹ : G) : G ⧸ N) = (k : G ⧸ N)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change QuotientGroup.mk' N a * QuotientGroup.mk' N k = _ at h
      rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, h, mul_inv_cancel_right]
    obtain ⟨c, hc, hck⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hck
    have hcK : c ∈ K := by
      have h := mul_mem hk (inv_mem (hNK.le hck))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
    have hc1 : c = 1 := hfix c hcK fun x hx => by
      have h : x * c * x⁻¹ = c := hc ⟨x, hx⟩
      calc x * c = x * c * x⁻¹ * x := by group
        _ = c * x := by rw [h]
    rw [hc1, inv_one, one_mul] at hck
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hck
  refine ⟨inferInstance, hcomp, hne, hcard, hcent, fun x hx hx1 y hy hxy => ?_⟩
  refine hcent y hy fun z hz => ?_
  have htop := zpowers_eq_top_of_prime_card hcard (g := (⟨x, hx⟩ : R.map (QuotientGroup.mk' N)))
    fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (htop ▸ Subgroup.mem_top (⟨z, hz⟩ : R.map (QuotientGroup.mk' N)))
  have hn' : x ^ n = z := congrArg Subtype.val hn
  rw [← hn']
  exact (Commute.zpow_left hxy n).eq

end CFSG.GroupTheory.SteinbergBK
