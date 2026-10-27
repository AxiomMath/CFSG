module

public import CFSG.HardMathSupport.Foote.E27.SporE81Sound
public import CFSG.HardMathSupport.Foote.E27.SplitIn

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Assembly (IsElemAbelian)

theorem exists_e81_of_mem_e27 {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hQ : Nat.card Q = 3 ^ (Nat.card G).factorization 3) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hgood : ∀ s ∈ Q, s ^ 3 = 1 → s ∉ zpowers z →
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E)
    {P : Subgroup G} (hP : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) {w : G} (hw : w ∈ P) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ w ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hQ hPp
  have hP'Q : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hP'e : IsElemAbelian 3 (P.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'27 : Nat.card (P.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27]
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hex : ∃ s' ∈ P.map (MulAut.conj g⁻¹).toMonoidHom, s' ∉ zpowers z := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ zpowers z := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    rw [hP'27, Nat.card_zpowers, hzo] at this
    omega
  obtain ⟨s', hs'P, hs'z⟩ := hex
  obtain ⟨E0, hE0, hE081, -, hzE0⟩ :=
    hgood s' (hP'Q hs'P) (hP'e.2 s' hs'P) hs'z
  have hw'P : g⁻¹ * w * g ∈ P.map (MulAut.conj g⁻¹).toMonoidHom :=
    ⟨w, hw, by simp [mul_assoc]⟩
  have hEw : ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ g⁻¹ * w * g ∈ E := by
    by_cases hwz : g⁻¹ * w * g ∈ zpowers z
    · exact ⟨E0, hE0, hE081, (Subgroup.zpowers_le.mpr hzE0) hwz⟩
    · obtain ⟨E, h1, h2, h3, -⟩ := hgood _ (hP'Q hw'P) (hP'e.2 _ hw'P) hwz
      exact ⟨E, h1, h2, h3⟩
  obtain ⟨E, hEe, hE81, hw'E⟩ := hEw
  refine ⟨E.map (MulAut.conj g).toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hEe, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81
  · exact ⟨_, hw'E, by simp [MulAut.conj_apply, mul_assoc]⟩

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_e81_data (h : E27Config X K R T z) (hz : z ∈ K) {G : Type*}
    [Group G] [Finite G] (e : ↥K ≃* G) {Q : Subgroup G} {zq : G}
    (hQ : Nat.card Q = 3 ^ (Nat.card G).factorization 3) (hz3 : zq ^ 3 = 1) (hz1 : zq ≠ 1)
    (hgood : ∀ s ∈ Q, s ^ 3 = 1 → s ∉ zpowers zq →
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧ zq ∈ E) : False := by
  have hRK : R ≤ K := h.le_of_mem hz
  have hRe : IsElemAbelian 3 (R.subgroupOf K) := isElemAbelian_subgroupOf K h.elem
  have hP : IsElemAbelian 3 ((R.subgroupOf K).map e.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hRe
  have hP27 : Nat.card ((R.subgroupOf K).map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, card_subgroupOf_of_le hRK, h.card_R]
  have hwP : e ⟨z, hz⟩ ∈ (R.subgroupOf K).map e.toMonoidHom :=
    ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.mpr h.z_mem, rfl⟩
  obtain ⟨E, hEe, hE81, hwE⟩ := exists_e81_of_mem_e27 hQ hz3 hz1 hgood hP hP27 hwP
  have hEc := hEe.1
  have hEk : ∀ d ∈ E, (e.symm d : ↥K) ∈ (E.map e.symm.toMonoidHom) := fun d hd => ⟨d, hd, rfl⟩
  let Ex : Subgroup X := (E.map e.symm.toMonoidHom).map K.subtype
  have hcard : Nat.card Ex = Nat.card E := by
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hle : Ex ≤ Subgroup.centralizer ({z} : Set X) := by
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun y : G => (e.symm y : ↥K).1)
      (IsMulCommutative.is_comm.comm (⟨d, hd⟩ : E) ⟨_, hwE⟩ |> congrArg Subtype.val)
    simpa using this
  have hp : IsPGroup 3 Ex := fun y => ⟨1, Subtype.ext (by
    obtain ⟨_, ⟨d, hd, rfl⟩, hy⟩ := y.2
    have h3 : d ^ 3 = 1 := hEe.2 d hd
    have : (e.symm d : ↥K) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    simpa [← hy] using congrArg Subtype.val this)⟩
  have := h.card_le_twentyseven_of_isPGroup hle hp
  omega

theorem E27Config.false_of_e81Check (h : E27Config X K R T z) (hz : z ∈ K) (D : E81Data)
    (hD : e81Check D = true) (hR : D.rOrd = D.qOrd)
    {J : Subgroup (Equiv.Perm (Fin D.n))} [Finite J]
    (hJ : ∀ l < D.pg.size, permOfArr D.n D.pg[l]! ∈ J)
    (hord : D.qOrd = 3 ^ (Nat.card J).factorization 3) (e : ↥K ≃* ↥J) : False := by
  obtain ⟨Q, R', zq, hQP, -, hQcard, hz3, hz1, hzQ, -, hRQ, hRcard, -, hgood⟩ :=
    e81_sound_card D hD J hJ
  have hRQeq : R' = Q := Subgroup.eq_of_le_of_card_ge hRQ (by rw [hQcard, hRcard, hR])
  subst hRQeq
  refine h.false_of_e81_data hz e (Q := R'.subgroupOf J) (zq := ⟨zq, hQP hzQ⟩) ?_ ?_ ?_ ?_
  · rw [card_subgroupOf_of_le hQP, hQcard, hord]
  · exact Subtype.ext (by simpa using hz3)
  · intro h1
    exact hz1 (congrArg Subtype.val h1)
  · intro s hsR hs3 hsz
    have hs3' : (s : Equiv.Perm (Fin D.n)) ^ 3 = 1 := by simpa using congrArg Subtype.val hs3
    have hsz' : (s : Equiv.Perm (Fin D.n)) ∉ Subgroup.zpowers zq := by
      rintro ⟨k, hk⟩
      exact hsz ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨E, hEJ, hEe, hE81, hsE, hzE⟩ :=
      hgood s (Subgroup.mem_subgroupOf.mp hsR) hs3' hsz'
    refine ⟨E.subgroupOf J, isElemAbelian_subgroupOf J hEe, ?_,
      Subgroup.mem_subgroupOf.mpr hsE, Subgroup.mem_subgroupOf.mpr hzE⟩
    rw [card_subgroupOf_of_le hEJ]
    exact hE81

end CFSG.HardMathSupport.Foote.E27
