module

public import CFSG.GH74.Uniqueness.SU.SU1CyclicIdx
public import CFSG.Walter.W67.Section5.MaxClass
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup

theorem card_le_four_of_index_two_cyclic {P : Type*} [Group P] [Finite P] {a : P}
    (ha : (zpowers a).index = 2) (E : Subgroup P) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  classical
  have : (zpowers a).Normal := Subgroup.normal_of_index_eq_two ha
  set N : Subgroup P := zpowers a with hN
  have h1 : Nat.card (N.subgroupOf E) * (N.subgroupOf E).index = Nat.card E :=
    Subgroup.card_mul_index _
  have h2 : (N.subgroupOf E).index ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal N E
    rwa [ha] at this
  have h3 : (N.subgroupOf E).index ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have h4 : Nat.card (N.subgroupOf E) ≤ 2 := by
    let f : N.subgroupOf E → {y : N // y ^ 2 = 1} := fun e =>
      ⟨⟨(e : E), (Subgroup.mem_subgroupOf.mp e.2)⟩, by
        apply Subtype.ext
        simp only [pow_two]
        exact hE _ e.1.2⟩
    have hf : Function.Injective f := by
      intro e e' h
      have := congrArg (fun y : {y : N // y ^ 2 = 1} => ((y : N) : P)) h
      exact Subtype.ext (Subtype.ext this)
    have h5 : Nat.card {y : N // y ^ 2 = 1} ≤ 2 := by
      have := Fintype.ofFinite N
      have := IsCyclic.card_pow_eq_one_le (α := N) (n := 2) (by norm_num)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact this
    exact (Nat.card_le_card_of_injective f hf).trans h5
  calc Nat.card E = Nat.card (N.subgroupOf E) * (N.subgroupOf E).index := h1.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h4 h3
    _ = 4 := by norm_num

theorem card_le_four_of_card_centralizer_le_four {P : Type} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {x : P} (hx : orderOf x = 2)
    (hc : Nat.card (centralizer ({x} : Set P)) ≤ 4) (E : Subgroup P)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ centralizer ({x} : Set P) := Subgroup.mem_centralizer_iff.mpr (by simp)
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hCp : IsPGroup 2 (centralizer ({x} : Set P)) := hP.to_subgroup _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hCp
  have hxd : 2 ∣ Nat.card (centralizer ({x} : Set P)) := by
    have : orderOf (⟨x, hxC⟩ : centralizer ({x} : Set P)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hx
    rw [← this]
    exact orderOf_dvd_natCard _
  have hk12 : k = 1 ∨ k = 2 := by
    have h1 : 2 ^ k ≤ 4 := hk ▸ hc
    have h2 : 2 ∣ 2 ^ k := hk ▸ hxd
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp at h2
    · have : k ≤ 2 := by
        by_contra hlt
        push Not at hlt
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      omega
  rcases hk12 with rfl | rfl
  ·
    have hPn : Nontrivial P := ⟨⟨x, 1, hx1⟩⟩
    obtain ⟨z, hz1⟩ : ∃ z : center P, z ≠ 1 := by
      have := hP.center_nontrivial
      exact exists_ne 1
    have hzC : (z : P) ∈ centralizer ({x} : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_center_iff.mp z.2 x
    have hz1' : (z : P) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzle : zpowers (z : P) ≤ centralizer ({x} : Set P) := Subgroup.zpowers_le.mpr hzC
    have hzcard : 2 ≤ Nat.card (zpowers (z : P)) := by
      rw [Nat.card_zpowers]
      have hp := orderOf_pos (z : P)
      have : orderOf (z : P) ≠ 1 := fun h => hz1' (orderOf_eq_one_iff.mp h)
      omega
    have heq : zpowers (z : P) = centralizer ({x} : Set P) :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hk]; simpa using hzcard)
    have hxz : x ∈ zpowers (z : P) := heq ▸ hxC
    have hxcen : ∀ y : P, x * y = y * x := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxz
      intro y
      rw [← hi]
      exact ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i) y)).symm
    have hall : centralizer ({x} : Set P) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hxcen y
    have : Nat.card P = 2 := by
      have h1 := Subgroup.card_top (G := P)
      rw [← hall, hk] at h1
      simpa using h1.symm
    calc Nat.card E ≤ Nat.card P := Subgroup.card_le_card_group E
      _ ≤ 4 := by omega
  ·
    have hmax := CFSG.Walter.W67.isMaximalClass_of_card_centralizer (p := 2) hP x hx
      (by rw [hk])
    obtain ⟨m, hm2, hm, hγ⟩ := hmax
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · have : m = 2 := by omega
      subst this
      calc Nat.card E ≤ Nat.card P := Subgroup.card_le_card_group E
        _ ≤ 4 := by rw [hm]; norm_num
    · have hnil : Group.IsNilpotent P := hP.isNilpotent
      have hcl1 : m - 1 ≤ Group.nilpotencyClass P := by
        by_contra hcon
        apply hγ
        rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
        omega
      obtain ⟨M, hMidx, hMcyc⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.exists_cyclic_index_two m hm3 P hm hcl1
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
      have hzM : zpowers (g : P) = M := by
        refine le_antisymm (Subgroup.zpowers_le.mpr g.2) (fun y hy => ?_)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
      exact card_le_four_of_index_two_cyclic (a := (g : P)) (by rw [hzM]; exact hMidx) E hE

theorem card_le_four_of_le_sylow {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (hS : IsPGroup 2 S) {x : H} (hxS : x ∈ S) (hx : orderOf x = 2)
    (hc : Nat.card ↥(S ⊓ centralizer ({x} : Set H)) ≤ 4) {E : Subgroup H} (hES : E ≤ S)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  set xP : S := ⟨x, hxS⟩ with hxP
  have hxPo : orderOf xP = 2 := by rw [hxP, Subgroup.orderOf_mk]; exact hx
  have hmap : (centralizer ({xP} : Set S)).map S.subtype =
      S ⊓ centralizer ({x} : Set H) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, Subgroup.coe_subtype, Subgroup.mem_inf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have := congrArg Subtype.val hz
      simpa [hxP] using this
    · rintro ⟨hy, hyc⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      apply Subtype.ext
      simpa [hxP] using hyc
  have hcP : Nat.card (centralizer ({xP} : Set S)) ≤ 4 := by
    have := Subgroup.card_map_of_injective (f := S.subtype) S.subtype_injective
      (K := centralizer ({xP} : Set S))
    rw [hmap] at this
    omega
  have hEP : ∀ e ∈ E.subgroupOf S, e * e = 1 := by
    intro e he
    apply Subtype.ext
    exact hE _ (Subgroup.mem_subgroupOf.mp he)
  have hPp : IsPGroup 2 S := hS
  have h := card_le_four_of_card_centralizer_le_four (P := S) hPp hxPo hcP (E.subgroupOf S) hEP
  have hcard : Nat.card (E.subgroupOf S) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  omega

theorem card_le_four_of_centralizer_two_subgroups {H : Type} [Group H] [Finite H] {x : H}
    (hx : orderOf x = 2)
    (hc : ∀ Q : Subgroup H, Q ≤ centralizer ({x} : Set H) → IsPGroup 2 Q → Nat.card Q ≤ 4)
    (E : Subgroup H) (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hxp : IsPGroup 2 (zpowers x) := by
    have hf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]; simp
  obtain ⟨S, hxS⟩ := hxp.exists_le_sylow
  have hEp : IsPGroup 2 E := by
    intro e
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hE _ e.2
  obtain ⟨S', hES'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S S'
  have hSS' : (S' : Subgroup H) = (S : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'S : E' ≤ (S : Subgroup H) := by
    rintro _ ⟨e, he, rfl⟩
    have := hES' he
    rw [hSS'] at this
    obtain ⟨s, hs, hse⟩ := this
    have h2 : g⁻¹ * e * g = s := by
      have h1 : g * s * g⁻¹ = e := by simpa [MulAut.conj_apply] using hse
      rw [← h1]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h2]
    exact hs
  have hE'e : ∀ e ∈ E', e * e = 1 := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * e * g⁻¹⁻¹ * (g⁻¹ * e * g⁻¹⁻¹) = g⁻¹ * (e * e) * g⁻¹⁻¹ := by group
      _ = 1 := by rw [hE e he]; group
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hSp : IsPGroup 2 (S : Subgroup H) := S.isPGroup'
  have hQ : Nat.card ↥((S : Subgroup H) ⊓ centralizer ({x} : Set H)) ≤ 4 :=
    hc _ inf_le_right (hSp.to_le inf_le_left)
  have := card_le_four_of_le_sylow hSp (hxS (Subgroup.mem_zpowers x)) hx hQ hE'S hE'e
  omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
