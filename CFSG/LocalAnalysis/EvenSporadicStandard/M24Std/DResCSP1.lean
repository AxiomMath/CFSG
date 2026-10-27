module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSV4

set_option linter.unusedSectionVars false

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

section Perfect

variable {Y : Type} [Group Y] [Finite Y]

theorem le_of_perfect_odd_complement {P Q W : Subgroup Y} (hP : ⁅P, P⁆ = P)
    (hQn : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q) (hW : W ≤ P) (hWodd : Odd (Nat.card W))
    (hPQW : ∀ p ∈ P, ∃ q ∈ Q, ∃ w ∈ W, p = q * w) : P ≤ Q := by
  have hN : (Q.subgroupOf P).Normal :=
    ⟨fun n hn g => mem_subgroupOf.2 (hQn g g.2 n (mem_subgroupOf.1 hn))⟩
  have hperf : Group.IsPerfect P := Subgroup.isPerfect_iff.2 hP
  let ψ : W →* P ⧸ Q.subgroupOf P := (QuotientGroup.mk' (Q.subgroupOf P)).comp (inclusion hW)
  have hψ : Function.Surjective ψ := by
    intro g
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨q, hq, w, hw, rfl⟩ := hPQW p hp
    refine ⟨⟨w, hw⟩, ?_⟩
    show QuotientGroup.mk (⟨w, hW hw⟩ : P) = QuotientGroup.mk ⟨q * w, hp⟩
    rw [QuotientGroup.eq]
    refine mem_subgroupOf.2 ?_
    show (w : Y)⁻¹ * (q * w) ∈ Q
    have := hQn w⁻¹ (P.inv_mem (hW hw)) q hq
    simpa [mul_assoc] using this
  have hodd : Odd (Nat.card (P ⧸ Q.subgroupOf P)) :=
    Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_surjective hψ)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (P ⧸ Q.subgroupOf P) := by
    by_contra hns
    have : Nontrivial (P ⧸ Q.subgroupOf P) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable (G := P ⧸ Q.subgroupOf P) hsolv
  intro p hp
  have : (QuotientGroup.mk (⟨p, hp⟩ : P) : P ⧸ Q.subgroupOf P) = 1 := Subsingleton.elim _ _
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 this)

end Perfect

section P1

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}

@[expose] def P1 (φ : K →* Equiv.Perm (Fin 6)) : Subgroup Y :=
  Subgroup.normalClosure (K0 φ : Set Y)

instance P1_normal : (P1 φ).Normal := Subgroup.normalClosure_normal

theorem K0_le_P1 : K0 φ ≤ P1 φ := Subgroup.subset_normalClosure

theorem P1_perfect (hY : CYHyp t K φ) : ⁅P1 φ, P1 φ⁆ = P1 φ := by
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  refine Subgroup.normalClosure_le_normal ?_
  intro y hy
  have : K0 φ ≤ ⁅P1 φ, P1 φ⁆ := by
    calc K0 φ = ⁅K0 φ, K0 φ⁆ := hY.quasi.perfect.symm
      _ ≤ ⁅P1 φ, P1 φ⁆ := Subgroup.commutator_mono K0_le_P1 K0_le_P1
  exact this hy

theorem centralizer_conj_mem {O : Subgroup Y} [O.Normal] {q : Y}
    (hq : q ∈ centralizer (O : Set Y)) (p : Y) : p * q * p⁻¹ ∈ centralizer (O : Set Y) := by
  rw [mem_centralizer_iff] at hq ⊢
  intro o ho
  have h1 := hq (p⁻¹ * o * p) (by simpa using Normal.conj_mem inferInstance o ho p⁻¹)
  calc o * (p * q * p⁻¹) = p * ((p⁻¹ * o * p) * q) * p⁻¹ := by group
    _ = p * (q * (p⁻¹ * o * p)) * p⁻¹ := by rw [h1]
    _ = p * q * p⁻¹ * o := by group

namespace CYHyp

variable (hY : CYHyp t K φ)
include hY

theorem lift_centralizer :
    ∀ x ∈ centralizer ({proj Y t} : Set (Yb Y)), ∃ γ ∈ centralizer ({t} : Set Y),
      proj Y γ = x := by
  have htK : t ∈ centralizer (K : Set Y) := mem_centralizer_iff.2 fun k hk => hY.comm k hk
  have hC' := centralizer_mk_fusionOddCore_eq hY.order hY.cent htK
  intro x hx
  have hle : K.map (proj Y) ⊔ zpowers (proj Y t) ≤ (centralizer ({t} : Set Y)).map (proj Y) := by
    refine sup_le (Subgroup.map_mono (le_sup_left.trans hY.cent.symm.le)) ?_
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.map_mono (le_sup_right.trans hY.cent.symm.le)
  rw [hC'] at hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 (hle hx)
  exact ⟨γ, hγ, rfl⟩

theorem P1_map_eq
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    (P1 φ).map (proj Y) = egaLayer (Yb Y) := by
  obtain ⟨f₁, f₂, hsw, hcard, hK0, hGOZ, hZO⟩ := hY.swap e
  have hEn := egaLayer_normal (Yb Y)
  have hsurj : Function.Surjective (proj Y) := QuotientGroup.mk'_surjective _
  refine le_antisymm ?_ ?_
  · rw [P1, Subgroup.map_normalClosure _ _ hsurj]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨γ, hγ, rfl⟩
    exact ((hK0 γ).1 hγ).2
  · set M : Subgroup (egaLayer (Yb Y)) := ((P1 φ).map (proj Y)).subgroupOf (egaLayer (Yb Y))
      with hM
    have hMn : M.Normal := Subgroup.Normal.subgroupOf (Subgroup.Normal.map inferInstance _ hsurj) _
    have hM' : (M.map e.toMonoidHom).Normal := hMn.map _ e.surjective
    obtain ⟨b, hb⟩ : ∃ b : alternatingGroup (Fin 6), b ≠ 1 := by
      have : Nontrivial (alternatingGroup (Fin 6)) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [card_alt6]; norm_num)
      exact exists_ne 1
    have hfb : f₁ b ≠ 1 := fun h => hb (f₁.injective (h.trans (map_one f₁).symm))
    have hmem : (f₁ b, b) ∈ M.map e.toMonoidHom := by
      refine ⟨e.symm (f₁ b, b), ?_, by simp⟩
      have hcomm : ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) ∈
          centralizer ({proj Y t} : Set (Yb Y)) := by
        rw [mem_centralizer_singleton_iff]
        have h1 := hsw.conj (e.symm (f₁ b, b))
        rw [MulEquiv.apply_symm_apply, hsw.inv] at h1
        have h2 : (⟨proj Y t * ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) * (proj Y t)⁻¹,
            hEn.conj_mem _ (e.symm (f₁ b, b)).2 _⟩ : egaLayer (Yb Y)) = e.symm (f₁ b, b) := by
          apply e.injective
          rw [h1, MulEquiv.apply_symm_apply]
        have h3 := congrArg Subtype.val h2
        simp only at h3
        calc ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) * proj Y t
            = proj Y t * ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) * (proj Y t)⁻¹ *
              proj Y t := by rw [h3]
          _ = proj Y t * ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) := by group
      obtain ⟨γ, hγ, hγx⟩ := hY.lift_centralizer _ hcomm
      have hγK0 : γ ∈ K0 φ := (hK0 γ).2 ⟨hγ, hγx ▸ (e.symm (f₁ b, b)).2⟩
      exact mem_subgroupOf.2 ⟨γ, K0_le_P1 hγK0, hγx⟩
    have htop : M.map e.toMonoidHom = ⊤ :=
      prod_normal_eq_top_of_simple alt6_hsimple (fun a => alt6_central) _ hfb hb hmem
    intro g hg
    have : e ⟨g, hg⟩ ∈ M.map e.toMonoidHom := by rw [htop]; trivial
    obtain ⟨m, hm, hme⟩ := this
    have : m = ⟨g, hg⟩ := e.injective hme
    rw [this] at hm
    exact mem_subgroupOf.1 hm

theorem P1_le_centralizer
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    P1 φ ≤ centralizer (fusionOddCore Y : Set Y) := by
  obtain ⟨f₁, f₂, hsw, hcard, hK0, hGOZ, hZO⟩ := hY.swap e
  have hOodd : Odd (Nat.card (fusionOddCore Y)) := odd_natCard_fusionOddCore Y
  have hEn := egaLayer_normal (Yb Y)
  have hmapP1 := hY.P1_map_eq e
  have hPn : (P1 φ).Normal := inferInstance
  have ht : t * t = 1 := by rw [← sq, ← hY.order, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have := hY.order
    rw [h, orderOf_one] at this
    omega
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hπt2 : proj Y t * proj Y t = 1 := by rw [← map_mul, ht, map_one]
  obtain ⟨c, hc2, hc1⟩ : ∃ c : alternatingGroup (Fin 6), c * c = 1 ∧ c ≠ 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 2
      (by rw [card_alt6]; norm_num)
    refine ⟨c, by rw [← sq]; exact hc ▸ pow_orderOf_eq_one c, ?_⟩
    intro h
    rw [h, orderOf_one] at hc
    omega
  set gbar : egaLayer (Yb Y) := e.symm (c, 1) with hgbar
  have hgbar2 : gbar * gbar = 1 := by
    rw [hgbar, ← map_mul]
    simp [hc2]
  obtain ⟨g, hgP1, hg2, hπg⟩ : ∃ g ∈ P1 φ, g * g = 1 ∧ proj Y g = (gbar : Yb Y) := by
    have : (gbar : Yb Y) ∈ (P1 φ).map (proj Y) := by rw [hmapP1]; exact gbar.2
    obtain ⟨g0, hg0, hg0π⟩ := Subgroup.mem_map.1 this
    obtain ⟨a, r, hr, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g0)
      (orderOf_pos_iff.2 (isOfFinOrder_of_finite _)).ne'
    obtain ⟨k, hk⟩ := hr
    have hπg : proj Y (g0 ^ r) = (gbar : Yb Y) := by
      rw [map_pow, hg0π, hk, pow_succ, pow_mul, show ((gbar : Yb Y)) ^ 2 = 1 from by
        rw [sq]; exact congrArg Subtype.val hgbar2, one_pow, one_mul]
    refine ⟨g0 ^ r, Subgroup.pow_mem _ hg0 r, ?_, hπg⟩
    have hsqO : (g0 ^ r) ^ 2 ∈ fusionOddCore Y := by
      have : proj Y ((g0 ^ r) ^ 2) = 1 := by
        rw [map_pow, hπg, sq]; exact congrArg Subtype.val hgbar2
      exact (QuotientGroup.eq_one_iff _).1 this
    have hodd : Odd (orderOf ((g0 ^ r) ^ 2)) :=
      Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hsqO)
    have h2 : ∃ k : ℕ, ((g0 ^ r) ^ 2) ^ (2 ^ k) = 1 := by
      refine ⟨a, ?_⟩
      have h1 : g0 ^ (2 ^ a * r) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
      calc ((g0 ^ r) ^ 2) ^ (2 ^ a) = (g0 ^ (2 ^ a * r)) ^ 2 := by
            simp only [← pow_mul]; congr 1; ring
        _ = 1 := by rw [h1, one_pow]
    have := E81Data.eq_one_of_pow_two_of_odd h2 hodd
    rwa [sq] at this
  have hconj := hsw.conj gbar
  have he : e gbar = (c, 1) := by rw [hgbar]; simp
  rw [he] at hconj
  simp only [map_one] at hconj
  set v : egaLayer (Yb Y) := e.symm (c, f₂ c) with hv
  have hπtg : (proj Y (t * g)) ^ 2 = (v : Yb Y) := by
    have e1 : (proj Y (t * g)) ^ 2 =
        (proj Y t * gbar * (proj Y t)⁻¹) * gbar := by
      rw [sq, map_mul, hπg]
      have : (proj Y t)⁻¹ = proj Y t := inv_eq_of_mul_eq_one_right hπt2
      rw [this]
      group
    rw [e1]
    have e2 : (⟨proj Y t * gbar * (proj Y t)⁻¹, hEn.conj_mem _ gbar.2 _⟩ : egaLayer (Yb Y)) =
        e.symm (1, f₂ c) := by
      apply e.injective
      rw [hconj, MulEquiv.apply_symm_apply]
    have e3 := congrArg Subtype.val e2
    simp only at e3
    rw [e3, hv, hgbar]
    simp [← Subgroup.coe_mul, ← map_mul]
  have hv1 : (proj Y (t * g)) ^ 2 ≠ 1 := by
    rw [hπtg]
    intro h
    have : v = 1 := Subtype.ext h
    have h' : (c, f₂ c) = (1, 1) := by
      have := congrArg e this
      rwa [hv, MulEquiv.apply_symm_apply, map_one] at this
    exact hc1 (Prod.ext_iff.1 h').1
  have hv4 : (proj Y (t * g)) ^ 4 = 1 := by
    have : (proj Y (t * g)) ^ 4 = ((proj Y (t * g)) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hπtg, ← Subgroup.coe_pow]
    have hv2 : v ^ 2 = 1 := by
      rw [hv, ← map_pow]
      have : (c, f₂ c) ^ 2 = 1 := by
        rw [sq, Prod.mk_mul_mk, hc2, ← map_mul, hc2, map_one]
        rfl
      rw [this, map_one]
    rw [hv2]
    rfl
  obtain ⟨x, h, hx2, hx1, htx, hhx, hth, hπx, hxz⟩ :=
    exists_dihedral_data hOodd ht hg2 hv1 hv4
  have hxP1 : x ∈ P1 φ := by
    have h1 : (t * g) ^ 2 ∈ P1 φ := by
      have : (t * g) ^ 2 = (t * g * t⁻¹) * g := by rw [sq, ht']; group
      rw [this]
      exact (P1 φ).mul_mem (hPn.conj_mem g hgP1 t) hgP1
    exact (zpowers_le.2 h1) hxz
  have hπx' : proj Y x = (v : Yb Y) := by
    have : proj Y x = proj Y ((t * g) ^ 2) := hπx
    rw [this, map_pow, hπtg]
  have hxK0 : x ∈ K0 φ :=
    (hK0 x).2 ⟨mem_centralizer_singleton_iff.2 htx, by rw [hπx']; exact v.2⟩
  have htx' : t ≠ x := fun h' => hY.not_mem (K0_le_K (h' ▸ hxK0))
  have hCO : ∀ o ∈ fusionOddCore Y, o * t = t * o → x * o = o * x := by
    intro o ho hot
    exact hY.quasi.central x hxK0 o (hGOZ o (mem_centralizer_singleton_iff.2 hot) ho)
  have hcent := centralizes_odd_of_v4 hOodd ht hx2 htx hhx hth hx1 ht1 htx' hCO
  set Q : Subgroup Y := P1 φ ⊓ centralizer (fusionOddCore Y : Set Y) with hQ
  have hxQ : x ∈ Q := ⟨hxP1, mem_centralizer_iff.2 fun o ho => (hcent o ho).symm⟩
  have hQn : ∀ p ∈ P1 φ, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := fun p hp q hq =>
    ⟨hPn.conj_mem q hq.1 p, centralizer_conj_mem hq.2 p⟩
  have hπQ : Q.map (proj Y) = egaLayer (Yb Y) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      have : proj Y q ∈ (P1 φ).map (proj Y) := ⟨q, hq.1, rfl⟩
      rwa [hmapP1] at this
    · set M : Subgroup (egaLayer (Yb Y)) := (Q.map (proj Y)).subgroupOf (egaLayer (Yb Y))
        with hM
      have hMn : M.Normal := by
        refine ⟨fun n hn g => ?_⟩
        obtain ⟨q0, hq0, hq0n⟩ := Subgroup.mem_map.1 (mem_subgroupOf.1 hn)
        have hg' : (g : Yb Y) ∈ (P1 φ).map (proj Y) := by rw [hmapP1]; exact g.2
        obtain ⟨p0, hp0, hp0g⟩ := Subgroup.mem_map.1 hg'
        refine mem_subgroupOf.2 ⟨p0 * q0 * p0⁻¹, hQn p0 hp0 q0 hq0, ?_⟩
        rw [map_mul, map_mul, map_inv, hp0g, hq0n]
        rfl
      have hM' : (M.map e.toMonoidHom).Normal := hMn.map _ e.surjective
      have hfc : f₂ c ≠ 1 := fun h' => hc1 (f₂.injective (h'.trans (map_one f₂).symm))
      have hmem : (c, f₂ c) ∈ M.map e.toMonoidHom := by
        refine ⟨v, ?_, by simp [hv]⟩
        exact mem_subgroupOf.2 ⟨x, hxQ, hπx'⟩
      have htop : M.map e.toMonoidHom = ⊤ :=
        prod_normal_eq_top_of_simple alt6_hsimple (fun a => alt6_central) _ hc1 hfc hmem
      intro g hg
      have : e ⟨g, hg⟩ ∈ M.map e.toMonoidHom := by rw [htop]; trivial
      obtain ⟨m, hm, hme⟩ := this
      have : m = ⟨g, hg⟩ := e.injective hme
      rw [this] at hm
      exact mem_subgroupOf.1 hm
  have hle : P1 φ ≤ Q := by
    refine le_of_perfect_odd_complement (P1_perfect hY) hQn
      (W := P1 φ ⊓ fusionOddCore Y) inf_le_left
      (Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_right)) ?_
    intro p hp
    have : proj Y p ∈ Q.map (proj Y) := by
      rw [hπQ, ← hmapP1]; exact ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.1 this
    refine ⟨q, hq, q⁻¹ * p, ⟨(P1 φ).mul_mem ((P1 φ).inv_mem hq.1) hp, ?_⟩, by group⟩
    have : proj Y (q⁻¹ * p) = 1 := by rw [map_mul, map_inv, hqp, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  exact hle.trans inf_le_right

end CYHyp

end P1

end CFSG.EvenSporadicStandard.M24Std.DRes
