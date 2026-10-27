module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoThree

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoThree
open scoped commutatorElement

section Card

variable {V : Type} [CommGroup V]

theorem card_sup_mul_card_le [Finite V] {A B C : Subgroup V} (hC : C ≤ A ⊓ B) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥C ≤ Nat.card ↥A * Nat.card ↥B := by
  let φ : ↥A × ↥B →* V :=
    (A.subtype.comp (MonoidHom.fst ↥A ↥B)) * (B.subtype.comp (MonoidHom.snd ↥A ↥B))
  have hrange : φ.range = A ⊔ B := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_sup']
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, rfl⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
  have hker : Nat.card ↥C ≤ Nat.card ↥φ.ker := by
    refine Nat.card_le_card_of_injective
      (fun c : ↥C => (⟨(⟨c.1, (hC c.2).1⟩, ⟨c.1⁻¹, B.inv_mem (hC c.2).2⟩), ?_⟩ : ↥φ.ker)) ?_
    · show (c.1 : V) * c.1⁻¹ = 1
      exact mul_inv_cancel _
    · intro c c' h
      have h1 := congrArg (fun z : ↥φ.ker => ((z.1.1 : ↥A) : V)) h
      exact Subtype.ext h1
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, Nat.card_prod] at h
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥C ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥φ.ker :=
        Nat.mul_le_mul_left _ hker
    _ = Nat.card ↥φ.ker * Nat.card ↥(A ⊔ B) := mul_comm _ _
    _ = Nat.card ↥A * Nat.card ↥B := h

theorem commV_map_conj (g : MulAut V) (Y : Subgroup (MulAut V)) :
    commV (Y.map (MulAut.conj g).toMonoidHom) = (commV Y).map g.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq Y g

theorem card_commV_of_natSection [Finite V] {Y : Subgroup (MulAut V)} {f : ℕ} (hf : 1 ≤ f)
    (hnat : IsNatSectionBy (slAct f) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y) = Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * f) := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hnat
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk, card_sl_model hf] at h1
  have h2 : Nat.card ↥((commV Y ⊓ fixV Y).subgroupOf (commV Y)) =
      Nat.card ↥(commV Y ⊓ fixV Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1.symm

end Card

section Nat

variable {V : Type} [CommGroup V] [Finite V]

theorem natSLTwo_of_classX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) {f : ℕ} (hf : 3 ≤ f) (hY : YSL Y f)
    (hnat : IsNatSectionBy (slAct f) Y (commV Y) (commV Y ⊓ fixV Y)) :
    IsNaturalSLTwoModule ↥(yuHol Y) f := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨hshort, halt | hsl⟩ := hX
  · exfalso
    obtain ⟨n, hn1, φ, ψ, hsum, hsurj, hker, hequiv⟩ := halt
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans (hY.center_eq_bot ▸ le_rfl)
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    obtain ⟨eY⟩ := hY
    have hcard := Nat.card_congr θ.toEquiv
    rw [Nat.card_congr eY.toEquiv, card_sl2_fq (by omega)] at hcard
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn : n = 1 := by omega
      subst hn
      have h3 : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [h3] at hcard
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : 16 ≤ 2 ^ (2 * f) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 4 * 15 ≤ 2 ^ f * (2 ^ (2 * f) - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    have hiso : alternatingGroup (Fin (2 * n + 1)) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f) :=
      θ.symm.trans eY
    obtain ⟨-, hf2⟩ := alt_sl2_iso (by omega) (by omega) hiso
    omega
  · obtain ⟨n, hn1, hsl'⟩ := hsl
    have h1 := card_commV_of_natSL hV hperf hshort hsl' hn1
    have h2 := card_commV_of_natSection (by omega : 1 ≤ f) hnat
    have hW : 0 < Nat.card ↥(commV Y ⊓ fixV Y) := Nat.card_pos
    have h3 : 2 ^ (2 * n) = 2 ^ (2 * f) := Nat.eq_of_mul_eq_mul_left hW (h1.symm.trans h2)
    have h4 : 2 * n = 2 * f := Nat.pow_right_injective (le_refl 2) h3
    have hnf : n = f := by omega
    subst hnf
    exact hsl'

end Nat

section Sylow

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_commV_eq_card_P_mul {K : Type*} [Field K] [Finite K] {G : Subgroup (MulAut V)}
    (D : NatData K G) : Nat.card ↥(commV G) = Nat.card ↥D.P * Nat.card K := by
  let ev : Multiplicative (Fin 2 → K) →* Multiplicative K :=
    { toFun := fun w => Multiplicative.ofAdd ((Multiplicative.toAdd w) 1)
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hev : Function.Surjective ev := fun k =>
    ⟨Multiplicative.ofAdd (Pi.single 1 (Multiplicative.toAdd k)), by simp [ev]⟩
  let h : ↥(commV G) →* Multiplicative K := ev.comp D.β
  have hsurj : Function.Surjective h := hev.comp D.surj
  have hker : h.ker = D.P.subgroupOf (commV G) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, NatData.mem_P]
    have hc : D.coord (u : V) = Multiplicative.toAdd (D.β u) := D.coord_of_mem u.2
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      rw [hc]
      exact ofAdd_eq_one.mp hu
    · rintro ⟨-, h0⟩
      rw [hc] at h0
      show Multiplicative.ofAdd (Multiplicative.toAdd (D.β u) 1) = 1
      rw [h0]
      rfl
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker] at h1
  have h2 : Nat.card ↥(D.P.subgroupOf (commV G)) = Nat.card ↥D.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.P_le_U).toEquiv
  have h3 : Nat.card (Multiplicative K) = Nat.card K :=
    Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)
  rw [h2, h3] at h1
  exact h1.symm

theorem card_commV_le_sylow (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hnat : IsNatSectionBy (slAct n) G (commV G) (commV G ⊓ fixV G))
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : Nat.card ↥T = 2 ^ n) :
    Nat.card ↥(commV G) ≤ Nat.card ↥(commV T) * 2 ^ n := by
  obtain ⟨D⟩ := exists_natData hnat
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g, hg⟩ := D.exists_conj_T_eq hTG (by rw [hT, hK])
  have h3 : 3 ≤ Nat.card ↥T := by
    rw [hT]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hP : (D.conj g).P ≤ commV T :=
    (D.conj g).P_le_commV_of_card hV h4 (B := T) (le_of_eq hg.symm) h3
  have hcard := card_commV_eq_card_P_mul (D.conj g)
  rw [hK] at hcard
  rw [hcard]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hP)

end Sylow

section Faithful

variable {V : Type} [CommGroup V] [Finite V]

theorem normal_le_center_or_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · left
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center Q) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).mp this
  · right
    have hNZ : ∀ x : Q, ∃ z ∈ Subgroup.center Q, QuotientGroup.mk' N x = QuotientGroup.mk' N z := by
      intro x
      have hx : QuotientGroup.mk' (Subgroup.center Q) x ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hz : n⁻¹ * x ∈ Subgroup.center Q := QuotientGroup.eq.mp hnx
      refine ⟨n⁻¹ * x, hz, ?_⟩
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, map_inv, hn1, inv_one, one_mul]
    have hcomm : commutator Q ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨z₁, hz₁, hx⟩ := hNZ x
      obtain ⟨z₂, hz₂, hy⟩ := hNZ y
      rw [← QuotientGroup.eq_one_iff (N := N), commutatorElement_def]
      change QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul, ← map_mul]
      have hc : z₁ * z₂ * z₁⁻¹ * z₂⁻¹ = 1 := by
        have := Subgroup.mem_center_iff.mp hz₁ z₂
        rw [← this]
        group
      rw [hc, map_one]
    rw [hQ.1] at hcomm
    exact top_le_iff.mp hcomm

omit [Finite V] in
theorem resHom_injective_of_quasisimple (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) :
    Function.Injective (CGT6.resHom L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have htriv : ∀ w ∈ commV L, (x : MulAut V) w = w := by
    intro w hw
    have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨w, hw⟩ : ↥(commV L)) : V)) hx
    simpa [CGT6.resHom_apply] using this
  have hxker : x ∈ (CGT6.resHom L).ker := hx
  rcases normal_le_center_or_top hq (CGT6.resHom L).normal_ker with hle | htop
  · have hxc : x ∈ Subgroup.center ↥L := hle hxker
    have hord : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hxc)
    rw [← Subgroup.orderOf_coe] at hord
    exact Subtype.ext (eq_one_of_trivial_on_commV hV x.2 hord htriv)
  · have hallt : ∀ y : ↥L, ∀ w ∈ commV L, (y : MulAut V) w = w := by
      intro y w hw
      have hy : y ∈ (CGT6.resHom L).ker := by rw [htop]; exact Subgroup.mem_top _
      have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨w, hw⟩ : ↥(commV L)) : V))
        (MonoidHom.mem_ker.mp hy)
      simpa [CGT6.resHom_apply] using this
    have : Group.IsPerfect ↥L := ⟨hq.1⟩
    have hbot : commV L ≤ ⊥ := by
      refine (commV_le_commOn_commV (Y := L)).trans ?_
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, u, hu, rfl⟩
      show g u * u⁻¹ ∈ (⊥ : Subgroup V)
      rw [Subgroup.mem_bot, hallt ⟨g, hg⟩ u hu, mul_inv_cancel]
    apply Subtype.ext
    ext v
    have hmem : (x : MulAut V) v * v⁻¹ ∈ commV L := Subgroup.subset_closure ⟨x, x.2, v, rfl⟩
    have h1 : (x : MulAut V) v * v⁻¹ = 1 := Subgroup.mem_bot.mp (hbot hmem)
    simpa using mul_inv_eq_one.mp h1

end Faithful

end CFSG.CGT.PushingUpLit.CGT6X.End3
