module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXWeakClosureFusionRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

namespace StrictRankStrongClosure

theorem exists_card_ker_range {A H : Type*} [Group A] [Group H] {p a : ℕ} (hp : p.Prime)
    (hA : Nat.card A = p ^ a) (f : A →* H) :
    ∃ b c, Nat.card f.ker = p ^ b ∧ Nat.card f.range = p ^ c ∧ b + c = a := by
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hA] at h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ h1)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ h1)
  refine ⟨b, c, hb, hc, ?_⟩
  rw [hb, hc, ← pow_add] at h1
  exact Nat.pow_right_injective hp.two_le h1

theorem le_pRank_of_range {A H : Type*} [Group A] [Group H] [Finite H] {p c : ℕ} (hp : 1 < p)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (f : A →* H)
    (hc : Nat.card f.range = p ^ c) : c ≤ CFSG.pRank p H := by
  have hel : IsElementaryAbelian p f.range :=
    { toIsMulCommutative := ⟨⟨fun u v => by
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp u.2
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp v.2
        exact Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hcomm])⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u => by
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp u.2
        exact Subtype.ext (by
          rw [Subgroup.coe_pow, ← ha, ← map_pow, hpow, map_one, Subgroup.coe_one]) }
  unfold CFSG.pRank
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨f.range, hel, hc⟩
  rintro k ⟨B, -, hB⟩
  have h1 : k < p ^ k := Nat.lt_pow_self hp
  have h2 : Nat.card B ≤ Nat.card H := Subgroup.card_le_card_group B
  omega

end StrictRankStrongClosure

open StrictRankStrongClosure

variable {D : Type*} [Group D]

theorem elementary_strict_rank_strong_closure_criterion [Finite D] {S E : Subgroup D}
    (hS : IsPGroup 2 S) (hES : E ≤ S) [(E.subgroupOf S).Normal] (hE : IsElementaryAbelian 2 E)
    (hrank : ∀ x ∈ S, x ∉ E →
      CFSG.pRank 2 (S ⧸ E.subgroupOf S) + CFSG.pRank 2 ↥(E ⊓ centralizer {x}) <
        CFSG.pRank 2 E) :
    (∀ g : D, CFSG.conjugate E g ≤ S → CFSG.conjugate E g = E) ∧
      ((∃ T : Sylow 2 (normalizer (E : Set D)),
          (T : Subgroup (normalizer (E : Set D))) = S.subgroupOf (normalizer (E : Set D))) →
        (∃ T : Sylow 2 D, (T : Subgroup D) = S) ∧ IsStronglyClosedIn S (E : Set D)) ∧
      ((∃ T : Sylow 2 D, (T : Subgroup D) = S) → IsStronglyClosedIn S (E : Set D)) := by
  classical
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hE2 : ∀ u ∈ E, u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian u hu
  have hEo : CFSG.Open.IsElemAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hE
  obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hrankE : CFSG.pRank 2 E = a := pRank_eq_of_elementary one_lt_two hEo ha
  have hSN : S ≤ normalizer (E : Set D) :=
    (normal_subgroupOf_iff_le_normalizer hES).mp inferInstance
  have hwc : ∀ g : D, CFSG.conjugate E g ≤ S → CFSG.conjugate E g = E := by
    intro g hFS
    by_contra hne
    have hmemF : ∀ y, y ∈ CFSG.conjugate E g ↔ g * y * g⁻¹ ∈ E := fun y => mem_conjugate_iff_wc
    have hFcard : Nat.card (CFSG.conjugate E g) = 2 ^ a := by rw [card_conjugate_wc, ha]
    obtain ⟨x, hxF, hxE⟩ : ∃ x ∈ CFSG.conjugate E g, x ∉ E := by
      by_contra h
      push Not at h
      exact hne (Subgroup.eq_of_le_of_card_ge h (ha.trans hFcard.symm).le)
    have hFcomm : ∀ u ∈ CFSG.conjugate E g, ∀ v ∈ CFSG.conjugate E g, u * v = v * u := by
      intro u hu v hv
      have h1 := hEcomm _ ((hmemF u).mp hu) _ ((hmemF v).mp hv)
      calc u * v = g⁻¹ * ((g * u * g⁻¹) * (g * v * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * v * g⁻¹) * (g * u * g⁻¹)) * g := by rw [h1]
        _ = v * u := by group
    have hF2 : ∀ u ∈ CFSG.conjugate E g, u * u = 1 := by
      intro u hu
      have h1 := hE2 _ ((hmemF u).mp hu)
      calc u * u = g⁻¹ * ((g * u * g⁻¹) * (g * u * g⁻¹)) * g := by group
        _ = 1 := by rw [h1]; group
    let f : CFSG.conjugate E g →* S ⧸ E.subgroupOf S :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion hFS)
    have hker : ∀ y : CFSG.conjugate E g, y ∈ f.ker ↔ (y : D) ∈ E := fun y =>
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hFS y)).trans mem_subgroupOf
    obtain ⟨b, c, hb, hc, hbc⟩ := exists_card_ker_range Nat.prime_two hFcard f
    have hc' : c ≤ CFSG.pRank 2 (S ⧸ E.subgroupOf S) :=
      le_pRank_of_range one_lt_two (fun u v => Subtype.ext (hFcomm _ u.2 _ v.2))
        (fun u => Subtype.ext (by simp [pow_two, hF2 _ u.2])) f hc
    let φ : f.ker →* ↥(E ⊓ centralizer {x}) :=
      { toFun := fun k => ⟨((k : CFSG.conjugate E g) : D), (hker _).mp k.2,
          mem_centralizer_singleton_iff.mpr (hFcomm _ (k : CFSG.conjugate E g).2 _ hxF)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := fun u v h => by
      have h' : ((φ u : ↥(E ⊓ centralizer {x})) : D) = φ v := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have hb' : b ≤ CFSG.pRank 2 ↥(E ⊓ centralizer {x}) := by
      refine le_pRank_of_range one_lt_two
        (fun u v => Subtype.ext (Subtype.ext (hFcomm _ (u : CFSG.conjugate E g).2 _
          (v : CFSG.conjugate E g).2)))
        (fun u => Subtype.ext (Subtype.ext (by
          simp [pow_two, hF2 _ (u : CFSG.conjugate E g).2]))) φ ?_
      rw [← hb]
      exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
    have := hrank x (hFS hxF) hxE
    omega
  have hstrong : (∃ T : Sylow 2 D, (T : Subgroup D) = S) → IsStronglyClosedIn S (E : Set D) := by
    rintro ⟨T, rfl⟩
    have key : ∀ t ∈ (T : Subgroup D), t ∉ E → (∃ h : D, h⁻¹ * t * h ∈ E) → False := by
      intro t ht htE hfus
      have hfr := (goldschmidt_weak_closure_fusion_rank_frontier T hES hEo hwc).2 t ht hfus
      have htE' : ∀ y ∈ E, t⁻¹ * y * t ∈ E := fun y hy => by
        simpa using (mem_normalizer_iff.mp (inv_mem (hSN ht)) y).mp hy
      set C := closure {x | ∃ e ∈ E, x = e⁻¹ * (t⁻¹ * e * t)} with hCdef
      let δ : E →* C := MonoidHom.mk'
        (fun y => ⟨(y : D)⁻¹ * (t⁻¹ * y * t), subset_closure ⟨y, y.2, rfl⟩⟩)
        (fun u v => Subtype.ext (by
          change ((u : D) * v)⁻¹ * (t⁻¹ * ((u : D) * v) * t) =
            (u : D)⁻¹ * (t⁻¹ * u * t) * ((v : D)⁻¹ * (t⁻¹ * v * t))
          have h1 := hEcomm _ (inv_mem v.2) _ (mul_mem (inv_mem u.2) (htE' _ u.2))
          calc ((u : D) * v)⁻¹ * (t⁻¹ * ((u : D) * v) * t)
              = (v : D)⁻¹ * ((u : D)⁻¹ * (t⁻¹ * u * t)) * (t⁻¹ * v * t) := by group
            _ = (u : D)⁻¹ * (t⁻¹ * u * t) * (v : D)⁻¹ * (t⁻¹ * v * t) := by rw [h1]
            _ = (u : D)⁻¹ * (t⁻¹ * u * t) * ((v : D)⁻¹ * (t⁻¹ * v * t)) := by group))
      have hkerδ : ∀ y : E, y ∈ δ.ker → t * y = y * t := by
        intro y hy
        have h1 : (y : D)⁻¹ * (t⁻¹ * y * t) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
        have h2 : t⁻¹ * y * t = y := (inv_mul_eq_one.mp h1).symm
        calc t * y = t * (t⁻¹ * y * t) := by rw [h2]
          _ = y * t := by group
      obtain ⟨b, c, hb, hc, hbc⟩ := exists_card_ker_range Nat.prime_two ha δ
      have hEcomm' : ∀ u v : E, u * v = v * u := fun u v => Subtype.ext (hEcomm _ u.2 _ v.2)
      have hE2' : ∀ u : E, u ^ 2 = 1 := fun u => Subtype.ext (by simp [pow_two, hE2 _ u.2])
      have hc' : c ≤ CFSG.pRank 2 C := le_pRank_of_range one_lt_two hEcomm' hE2' δ hc
      let ψ : δ.ker →* ↥(E ⊓ centralizer {t}) :=
        { toFun := fun k => ⟨((k : E) : D), (k : E).2,
            mem_centralizer_singleton_iff.mpr (hkerδ _ k.2).symm⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hψ : Function.Injective ψ := fun u v h => by
        have h' : ((ψ u : ↥(E ⊓ centralizer {t})) : D) = ψ v := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
      have hb' : b ≤ CFSG.pRank 2 ↥(E ⊓ centralizer {t}) := by
        refine le_pRank_of_range one_lt_two (fun u v => Subtype.ext (hEcomm' _ _))
          (fun u => Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hE2' _))
          ψ ?_
        rw [← hb]
        exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
      have := hrank t ht htE
      omega
    refine ⟨fun e he => hES he, fun e he g hgS => ?_⟩
    by_contra htE
    exact key _ hgS htE ⟨g⁻¹, by simpa [mul_assoc] using he⟩
  have hsyl : (∃ T : Sylow 2 (normalizer (E : Set D)),
      (T : Subgroup (normalizer (E : Set D))) = S.subgroupOf (normalizer (E : Set D))) →
      ∃ T : Sylow 2 D, (T : Subgroup D) = S := by
    rintro ⟨T, hT⟩
    obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
    rcases eq_or_lt_of_le hSQ with h | hlt
    · exact ⟨Q, h.symm⟩
    exfalso
    have := Q.isPGroup'.isNilpotent
    have htop : S.subgroupOf Q < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hlt.ne (le_antisymm hlt.le (subgroupOf_eq_top.mp h))
    obtain ⟨z, hz, hzS⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ htop)
    have hzS' : (z : D) ∉ S := fun h => hzS (mem_subgroupOf.mpr h)
    have hconj : CFSG.conjugate E z ≤ S := by
      intro w hw
      rw [mem_conjugate_iff_wc] at hw
      have h1 := (mem_normalizer_iff.mp (inv_mem hz) ⟨_, hSQ (hES hw)⟩).mp
        (mem_subgroupOf.mpr (hES hw))
      rw [mem_subgroupOf] at h1
      simpa [mul_assoc] using h1
    have hzN : (z : D) ∈ normalizer (E : Set D) := conjugate_eq_self_iff_wc.mp (hwc _ hconj)
    have hPQ : S ⊔ zpowers (z : D) ≤ Q := sup_le hSQ (zpowers_le.mpr z.2)
    have hPN : S ⊔ zpowers (z : D) ≤ normalizer (E : Set D) := sup_le hSN (zpowers_le.mpr hzN)
    have hPp : IsPGroup 2 ((S ⊔ zpowers (z : D)).subgroupOf (normalizer (E : Set D))) :=
      (Q.isPGroup'.to_le hPQ).comap_subtype
    have hle : (T : Subgroup (normalizer (E : Set D))) ≤
        (S ⊔ zpowers (z : D)).subgroupOf (normalizer (E : Set D)) := by
      rw [hT]
      intro w hw
      exact mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hw))
    have heq := T.is_maximal' hPp hle
    have hzP : (⟨z, hzN⟩ : normalizer (E : Set D)) ∈
        (S ⊔ zpowers (z : D)).subgroupOf (normalizer (E : Set D)) :=
      mem_subgroupOf.mpr (mem_sup_right (mem_zpowers _))
    rw [heq, hT, mem_subgroupOf] at hzP
    exact hzS' hzP
  refine ⟨hwc, fun h => ?_, hstrong⟩
  have hT := hsyl h
  exact ⟨hT, hstrong hT⟩

end CFSG.LocalAnalysis.GorensteinLyons
