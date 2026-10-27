module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Covering
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Omega
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14ZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Cover

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

namespace FourGen

theorem false_of_not_mem_fourGroup (hz : FourGen Q z) (h : Setting J Q B) {w : J}
    (hwQ : w ∈ (Q : Subgroup J)) (hw : w * w = centralElt J)
    (hwz : w * z = z * w) (hrank : CFSG.Open.pRank 2 (quasiNormalizer w) ≤ 2)
    (hQX : ¬ (Q : Subgroup J) ≤ quasiNormalizer w)
    (hΩ : ∀ x ∈ (Q : Subgroup J), x * w = w * x → x * x = 1 → x ∈ fourGroup z)
    {t : J} (htQ : t ∈ (Q : Subgroup J)) (htX : t ∈ quasiNormalizer w) (ht : t * t = 1)
    (htV : t ∉ fourGroup z) : False := by
  have hzz := hz.mul_self
  have hzX : z ∈ quasiNormalizer w := h.mem_quasiNormalizer_of_mul_eq hw hwz.symm
  have htz : t * z * t⁻¹ = centralElt J * z := (hz.conj_eq h htQ).resolve_left fun h1 => by
    have htz' : t * z = z * t := by
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h1]
    have := hz.three_le_pRank h (h.centralElt_mem_quasiNormalizer w) hzX htX ht htz' htV
    omega
  obtain ⟨s, hs⟩ : ∃ s, s = t * z := ⟨_, rfl⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hss : s * s = centralElt J := by
    calc s * s = (t * z * t⁻¹) * z := by rw [hs, htinv]; group
      _ = centralElt J := by rw [htz, mul_assoc, hzz, mul_one]
  have hszs : s * z * s⁻¹ = centralElt J * z := by
    rw [← htz, hs]
    group
  have hs_ne : s * z ≠ z * s := by
    intro h'
    apply h.centralElt_ne_one
    have h2 : s * z * s⁻¹ = z := by rw [h', mul_inv_cancel_right]
    rw [hszs] at h2
    exact mul_eq_right.mp h2
  have hsQ : s ∈ (Q : Subgroup J) := hs ▸ (Q : Subgroup J).mul_mem htQ hz.mem
  have hsX : s ∈ quasiNormalizer w := hs ▸ (quasiNormalizer w).mul_mem htX hzX
  have hsw : s * w * s⁻¹ = centralElt J * w :=
    (h.conj_eq_of_mem_quasiNormalizer hw hsX).resolve_left fun h1 =>
      hz.mul_ne_of_not_commute h hsQ hss hs_ne hwQ hw hwz hΩ (by
        calc s * w = s * w * s⁻¹ * s := by group
          _ = w * s := by rw [h1])
  set T := (Q : Subgroup J) ⊓ quasiNormalizer w with hT
  have hQT : ¬ (Q : Subgroup J) ≤ T := fun hle => hQX (hle.trans inf_le_right)
  obtain ⟨r₀, hr₀Q, hr₀T, hr₀N⟩ := exists_mem_normalizer_not_mem Q.isPGroup' inf_le_left hQT
  have htT : t ∈ T := ⟨htQ, htX⟩
  obtain ⟨r, hrQ, hrT, hrN, hrz⟩ : ∃ r ∈ (Q : Subgroup J), r ∉ T ∧
      r ∈ Subgroup.normalizer (T : Set J) ∧ r * z = z * r := by
    rcases hz.conj_eq h hr₀Q with h1 | h1
    · refine ⟨r₀, hr₀Q, hr₀T, hr₀N, ?_⟩
      calc r₀ * z = r₀ * z * r₀⁻¹ * r₀ := by group
        _ = z * r₀ := by rw [h1]
    · refine ⟨r₀ * t, (Q : Subgroup J).mul_mem hr₀Q htQ, fun hmem => hr₀T ?_,
        Subgroup.mul_mem _ hr₀N (Subgroup.le_normalizer htT), ?_⟩
      · have h2 := T.mul_mem hmem (T.inv_mem htT)
        rwa [mul_inv_cancel_right] at h2
      · have h2 : r₀ * t * z * (r₀ * t)⁻¹ = z := by
          calc r₀ * t * z * (r₀ * t)⁻¹ = r₀ * (t * z * t⁻¹) * r₀⁻¹ := by group
            _ = centralElt J * (r₀ * z * r₀⁻¹) := by rw [htz, h.mul_central_left]; group
            _ = z := by rw [h1, ← mul_assoc, h.centralElt_mul_self, one_mul]
        calc r₀ * t * z = r₀ * t * z * (r₀ * t)⁻¹ * (r₀ * t) := by group
          _ = z * (r₀ * t) := by rw [h2]
  have hrX : r ∉ quasiNormalizer w := fun hrX => hrT ⟨hrQ, hrX⟩
  obtain ⟨v, hv⟩ : ∃ v, v = r * w * r⁻¹ := ⟨_, rfl⟩
  have hwT : w ∈ T := ⟨hwQ, Subgroup.le_normalizer (Subgroup.mem_zpowers w)⟩
  have hvT : v ∈ T := hv ▸ (Subgroup.mem_normalizer_iff.mp hrN w).mp hwT
  have hvQ : v ∈ (Q : Subgroup J) := hvT.1
  have hvv : v * v = centralElt J := by
    rw [hv]
    calc r * w * r⁻¹ * (r * w * r⁻¹) = r * (w * w) * r⁻¹ := by group
      _ = centralElt J := by rw [hw, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
  have hvz : v * z = z * v := by
    have h1 : Commute v z := by
      rw [hv]
      exact ((show Commute r z from hrz).mul_left (show Commute w z from hwz)).mul_left
        (show Commute r z from hrz).inv_left
    exact h1.eq
  have hΩv : ∀ y ∈ (Q : Subgroup J), y * v = v * y → y * y = 1 → y ∈ fourGroup z := by
    intro y hyQ hyv hyy
    have h1 : r⁻¹ * y * r ∈ fourGroup z := hΩ _
      ((Q : Subgroup J).mul_mem ((Q : Subgroup J).mul_mem ((Q : Subgroup J).inv_mem hrQ) hyQ)
        hrQ)
      (by
        calc r⁻¹ * y * r * w = r⁻¹ * (y * v) * r := by rw [hv]; group
          _ = r⁻¹ * (v * y) * r := by rw [hyv]
          _ = w * (r⁻¹ * y * r) := by rw [hv]; group)
      (by
        calc r⁻¹ * y * r * (r⁻¹ * y * r) = r⁻¹ * (y * y) * r := by group
          _ = 1 := by rw [hyy, mul_one, inv_mul_cancel])
    have h2 := hz.conj_mem_fourGroup h hrQ h1
    rwa [show r * (r⁻¹ * y * r) * r⁻¹ = y by group] at h2
  have hsXv : s ∈ quasiNormalizer v := by
    have h1 := (h.mem_quasiNormalizer_conj_iff hw r⁻¹ s).mpr
      ((Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set J)).inv_mem hrN) s).mp
        ⟨hsQ, hsX⟩).2
    rwa [inv_inv, ← hv] at h1
  have hsv : s * v * s⁻¹ = centralElt J * v :=
    (h.conj_eq_of_mem_quasiNormalizer hvv hsXv).resolve_left fun h1 =>
      hz.mul_ne_of_not_commute h hsQ hss hs_ne hvQ hvv hvz hΩv (by
        calc s * v = s * v * s⁻¹ * s := by group
          _ = v * s := by rw [h1])
  have hswv : s * (w * v) * s⁻¹ = w * v := by
    calc s * (w * v) * s⁻¹ = (s * w * s⁻¹) * (s * v * s⁻¹) := by group
      _ = w * v := by rw [hsw, hsv, h.central_mul_central]
  have hvw : v * w = w * v := by
    rcases h.conj_eq_of_mem_quasiNormalizer hw hvT.2 with h1 | h1
    · calc v * w = v * w * v⁻¹ * v := by group
        _ = w * v := by rw [h1]
    exfalso
    obtain ⟨y, hy⟩ : ∃ y, y = s * (w * v) := ⟨_, rfl⟩
    have hvw' : v * w = centralElt J * (w * v) := by
      calc v * w = v * w * v⁻¹ * v := by group
        _ = centralElt J * (w * v) := by rw [h1, mul_assoc]
    have hyw : y * w = w * y := by
      have h2 : y * w * y⁻¹ = w := by
        calc y * w * y⁻¹ = (s * w) * ((v * w * v⁻¹) * (w⁻¹ * s⁻¹)) := by rw [hy]; group
          _ = (s * w) * (centralElt J * (w * (w⁻¹ * s⁻¹))) := by
              rw [h1, mul_assoc (centralElt J) w]
          _ = centralElt J * (s * w * s⁻¹) := by rw [h.mul_central_left]; group
          _ = w := by rw [hsw, ← mul_assoc, h.centralElt_mul_self, one_mul]
      calc y * w = y * w * y⁻¹ * y := by group
        _ = w * y := by rw [h2]
    have hyy : y * y = 1 := by
      calc y * y = (s * (w * v) * s⁻¹) * ((s * s) * (w * v)) := by rw [hy]; group
        _ = centralElt J * ((w * v) * (w * v)) := by rw [hswv, hss, h.mul_central_left]
        _ = centralElt J * (w * ((v * w) * v)) := by group
        _ = centralElt J * (centralElt J * (w * ((w * v) * v))) := by
            rw [hvw', mul_assoc (centralElt J) (w * v) v, h.mul_central_left w]
        _ = (w * w) * (v * v) := by rw [← mul_assoc, h.centralElt_mul_self, one_mul]; group
        _ = 1 := by rw [hw, hvv, h.centralElt_mul_self]
    have hyQ : y ∈ (Q : Subgroup J) :=
      hy ▸ (Q : Subgroup J).mul_mem hsQ ((Q : Subgroup J).mul_mem hwQ hvQ)
    have hyV := hΩ y hyQ hyw hyy
    apply hs_ne
    have h3 : Commute (y * v⁻¹ * w⁻¹) z :=
      ((show Commute y z from hz.mul_comm_of_mem_fourGroup h hyV).mul_left
        (show Commute v z from hvz).inv_left).mul_left (show Commute w z from hwz).inv_left
    rw [show y * v⁻¹ * w⁻¹ = s by rw [hy]; group] at h3
    exact h3.eq
  have hwvV : w * v ∈ fourGroup z := hΩ _ ((Q : Subgroup J).mul_mem hwQ hvQ)
    (by
      calc w * v * w = w * (v * w) := by group
        _ = w * (w * v) := by rw [hvw])
    (by
      calc w * v * (w * v) = w * (v * w) * v := by group
        _ = w * (w * v) * v := by rw [hvw]
        _ = (w * w) * (v * v) := by group
        _ = 1 := by rw [hw, hvv, h.centralElt_mul_self])
  have hwvZ : w * v ∉ Subgroup.center J := by
    intro hc
    apply hrX
    rw [h.mem_normalizer_zpowers_iff hw]
    have heq : r * w * r⁻¹ * w⁻¹ = (w * v) * (w * w)⁻¹ := by
      rw [← hv, ← hvw]
      group
    rw [heq]
    refine (Subgroup.center J).mul_mem hc ((Subgroup.center J).inv_mem ?_)
    rw [hw]
    exact h.centralElt_mem_center
  have hsc : s * (w * v) * s⁻¹ = centralElt J * (w * v) := by
    have hwv1 : w * v ≠ 1 := fun h1 => hwvZ (by rw [h1]; exact (Subgroup.center J).one_mem)
    rcases hz.eq_of_mem_fourGroup_of_ne_one h hwvV hwv1 with h2 | h2 | h2
    · exact (hwvZ (by rw [h2]; exact h.centralElt_mem_center)).elim
    · rw [h2]
      exact hszs
    · rw [h2, show s * (centralElt J * z) * s⁻¹ = centralElt J * (s * z * s⁻¹) by
        rw [h.mul_central_left]; group, hszs]
  rw [hswv] at hsc
  exact h.centralElt_ne_one (mul_eq_right.mp hsc.symm)

theorem exists_cover_of_sylowPlaced (hz : FourGen Q z) (h : Setting J Q B)
    {w : J} (hwQ : w ∈ (Q : Subgroup J)) (hw : w * w = centralElt J)
    (hwz : w * z = z * w) (hrank : CFSG.Open.pRank 2 (quasiNormalizer w) ≤ 2)
    {N : Subgroup J} (hNX : N ≤ quasiNormalizer w)
    (hXN : quasiNormalizer w ≤ Subgroup.normalizer (N : Set J)) (hNodd : Odd (Nat.card N))
    (hNB : ¬ N ≤ B) (hQX : ¬ (Q : Subgroup J) ≤ quasiNormalizer w)
    (hmax : ∀ P ≤ Subgroup.normalizer (fourGroup z : Set J) ⊓ quasiNormalizer w,
      IsPGroup 2 P → Nat.card P ≤ Nat.card ((Q : Subgroup J) ⊓ quasiNormalizer w : Subgroup J)) :
    ∃ W : Subgroup J, (∀ t ∈ quasiNormalizer w, orderOf t = 2 → t ∈ W) ∧
      ∀ y ∈ W, y * y ≠ centralElt J := by
  have hΩ : ∀ x ∈ (Q : Subgroup J), x * w = w * x → x * x = 1 → x ∈ fourGroup z :=
    fun x hxQ hxw hx =>
      hz.mem_fourGroup_of_commute h (h.sylow_le hwQ) hw hwz hrank hNX hXN hNodd hNB hxQ hxw hx
  refine hz.exists_cover_of_isolated h hw hwz (hz.card_le_of_sylowPlaced h hw hwz hmax hΩ)
    fun x hx hxx => ?_
  by_contra hxV
  exact hz.false_of_not_mem_fourGroup h hwQ hw hwz hrank hQX hΩ hx.1 hx.2 hxx hxV

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
