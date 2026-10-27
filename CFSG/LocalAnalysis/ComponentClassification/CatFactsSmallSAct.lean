module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.UnbalancedLayer

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] {E : Subgroup G} [Finite E] {x : G}
    (h : ∀ g ∈ E, x * g * x⁻¹ ∈ E) : x ∈ normalizer (E : Set G) := by
  have hle : E.map (MulAut.conj x).toMonoidHom ≤ E := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  have heq : E.map (MulAut.conj x).toMonoidHom = E :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := by
      have h2 : x * w * x⁻¹ = x * y * x⁻¹ := hwy
      simpa using h2
    rwa [← this]

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem hyp_S_le_N : h.S ≤ normalizer (h.J : Set H) := fun _ hs => (h.S_le hs).2

@[expose] noncomputable def sAct : ↥h.S →* MulAut (OddBar h.J) :=
  (oddBarConj h.J).comp (inclusion (hyp_S_le_N h))

theorem sAct_apply (s : h.S) : sAct h s = oddBarConj h.J ⟨s, hyp_S_le_N h s.2⟩ := rfl

omit [Finite H] in
theorem oddBarConj_one_of_mem_kernel {L : Subgroup H} {g : ↥(normalizer (L : Set H))}
    (hg : (g : H) ∈ coreActionKernel L) : oddBarConj L g = 1 := by
  obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hg
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have hj : (g : H) * y * (g : H)⁻¹ ∈ L := (mem_normalizer_iff.mp g.2 y).mp y.2
  obtain ⟨o, ho, hoe⟩ := mem_map.mp (hc _ hj)
  convert ho using 1
  apply Subtype.ext
  rw [subtype_apply] at hoe
  rw [hoe]
  simp only [coe_mul, coe_inv]
  group

omit [Finite H] in
theorem oddBarConj_of_mem {L : Subgroup H} (k : L) (hk : (k : H) ∈ normalizer (L : Set H)) :
    oddBarConj L ⟨k, hk⟩ = MulAut.conj (k : L ⧸ pPrimeCore 2 L) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem sAct_eq_one_iff (s : h.S) : sAct h s = 1 ↔ (s : H) ∈ h.P :=
  ⟨fun hs => ⟨s.2, mem_coreActionKernel_of_oddBarConj_eq_one hs⟩,
    fun hs => oddBarConj_one_of_mem_kernel hs.2⟩

theorem sAct_of_mem_J (s : h.S) (hs : (s : H) ∈ h.J) :
    sAct h s = MulAut.conj ((⟨s, hs⟩ : h.J) : OddBar h.J) :=
  oddBarConj_of_mem (L := h.J) ⟨s, hs⟩ (hyp_S_le_N h s.2)

theorem isPGroup_S : IsPGroup 2 h.S := by
  obtain ⟨R, hR⟩ := h.S_sylow
  have hle : h.S ≤ centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) := h.S_le
  have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set H) ⊓
      normalizer (h.J : Set H))) := hR ▸ R.isPGroup'
  exact h1.of_equiv (subgroupOfEquivOfLe hle)

theorem exists_sylow_D : ∃ T : Sylow 2 ↥h.J, (T : Subgroup h.J) = h.D.subgroupOf h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) with hX
  obtain ⟨R, hR⟩ := h.S_sylow
  have hJX : h.J ≤ X := le_inf h.J_le le_normalizer
  have hK : (h.J.subgroupOf X).Normal := ⟨fun k hk x => by
    rw [mem_subgroupOf] at hk ⊢
    exact (mem_normalizer_iff.1 x.2.2 k).1 hk⟩
  let T₀ := QuasiDihedralFusion.sylowInfNormal R (h.J.subgroupOf X)
  let e : ↥(h.J.subgroupOf X) ≃* h.J := subgroupOfEquivOfLe hJX
  refine ⟨T₀.mapSurjective (f := e.toMonoidHom) (fun y => ⟨e.symm y, by simp⟩),
    (Sylow.coe_mapSurjective _ T₀).trans ?_⟩
  rw [QuasiDihedralFusion.sylowInfNormal_coe, hR]
  ext j
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf] at hk
    rw [mem_subgroupOf]
    exact ⟨hk, (mem_subgroupOf.1 k.2)⟩
  · intro hj
    rw [mem_subgroupOf] at hj
    refine ⟨⟨⟨j, hJX j.2⟩, mem_subgroupOf.2 j.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf]
    exact hj.1

theorem exists_sylow_Dbar : ∃ T : Sylow 2 (OddBar h.J),
    (T : Subgroup (OddBar h.J)) = (h.D.subgroupOf h.J).map
      (QuotientGroup.mk' (pPrimeCore 2 h.J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_D h
  exact ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hT]⟩

theorem mem_D_sup_P_iff_inner (hZ : center (OddBar h.J) = ⊥) (s : h.S) :
    sAct h s ∈ (MulAut.conj : OddBar h.J →* MulAut (OddBar h.J)).range ↔
      (s : H) ∈ h.D ⊔ h.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 h.J)
  have hDS : h.D ≤ h.S := inf_le_left
  have hPS : h.P ≤ h.S := inf_le_left
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨Tb, hTb⟩ := exists_sylow_Dbar h
    have hxT : ∀ y ∈ (Tb : Subgroup (OddBar h.J)), x * y * x⁻¹ ∈ (Tb : Subgroup (OddBar h.J)) := by
      intro y hy
      rw [hTb] at hy ⊢
      obtain ⟨t, ht, rfl⟩ := hy
      rw [SetLike.mem_coe, mem_subgroupOf] at ht
      have h1 : x * π t * x⁻¹ = MulAut.conj x (π t) := rfl
      rw [h1, hx, sAct_apply, QuotientGroup.mk'_apply, oddBarConj_apply_mk]
      refine ⟨_, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf]
      have h1 : (s : H) * t * (s : H)⁻¹ ∈ h.S :=
        h.S.mul_mem (h.S.mul_mem s.2 ht.1) (h.S.inv_mem s.2)
      exact mem_inf.2 ⟨h1, (mem_normalizer_iff.1 (hyp_S_le_N h s.2) t).1 t.2⟩
    have hxN : x ∈ normalizer ((Tb : Subgroup (OddBar h.J)) : Set (OddBar h.J)) :=
      mem_normalizer_of_conj_le hxT
    obtain ⟨k, hk⟩ := isPGroup_S h s
    have hxk : x ^ 2 ^ k = 1 := by
      have h2 : MulAut.conj (x ^ 2 ^ k) = 1 := by rw [map_pow, hx, ← map_pow, hk, map_one]
      have h3 : x ^ 2 ^ k ∈ center (OddBar h.J) := by
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (OddBar h.J) => φ g) h2
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * x ^ 2 ^ k = x ^ 2 ^ k * g * (x ^ 2 ^ k)⁻¹ * x ^ 2 ^ k := by rw [this]
          _ = x ^ 2 ^ k * g := inv_mul_cancel_right _ _
      rw [hZ, mem_bot] at h3
      exact h3
    have hx2 : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card_dvd_pow (n := k) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hxk)
    have hxD : x ∈ (Tb : Subgroup (OddBar h.J)) := by
      have hsup : IsPGroup 2 ↥((Tb : Subgroup (OddBar h.J)) ⊔ zpowers x) :=
        IsPGroup.to_sup_of_normal_left' Tb.isPGroup' hx2 (zpowers_le.2 hxN)
      have heq := Tb.is_maximal' hsup le_sup_left
      rw [← heq]
      exact mem_sup_right (mem_zpowers x)
    rw [hTb] at hxD
    obtain ⟨d, hd, rfl⟩ := hxD
    rw [SetLike.mem_coe, mem_subgroupOf] at hd
    let dS : h.S := ⟨d, hd.1⟩
    have h1 : sAct h (s * dS⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hx, sAct_of_mem_J h dS d.2]
      exact mul_inv_cancel _
    have hP := (sAct_eq_one_iff h _).1 h1
    have hs : (s : H) = ((s * dS⁻¹ : h.S) : H) * d := by
      simp [dS]
    rw [hs]
    exact mul_mem (mem_sup_right hP) (mem_sup_left hd)
  · intro hs
    have hle : (h.D ⊔ h.P).subgroupOf h.S ≤
        (MulAut.conj : OddBar h.J →* MulAut (OddBar h.J)).range.comap (sAct h) := by
      rw [subgroupOf_sup hDS hPS]
      refine sup_le (fun d hd => ?_) (fun p hp => ?_)
      · rw [mem_subgroupOf] at hd
        rw [mem_comap, sAct_of_mem_J h d hd.2]
        exact ⟨_, rfl⟩
      · rw [mem_subgroupOf] at hp
        rw [mem_comap, (sAct_eq_one_iff h p).2 hp]
        exact one_mem _
    exact hle (mem_subgroupOf.2 hs)

end CFSG.ComponentClassification.CatFactsSmall
