module

public import CFSG.CGT.PushingUpLit.A78.L3Local
public import CFSG.CGT.PushingUpLit.A78.Sp4Transport
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

theorem le_of_normalizes_sylow {P W : Subgroup G} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (hW : IsPGroup 2 W) (hWN : W ≤ Subgroup.normalizer (P : Set G)) : W ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQset : ((hP.toSylow hPi : Sylow 2 G) : Set G) = (P : Set G) := by
    ext x
    exact IsPGroup.mem_toSylow hP hPi
  have hWN' : W ≤ Subgroup.normalizer ((hP.toSylow hPi : Sylow 2 G) : Set G) := by
    rwa [hQset]
  have h1 := hW.inf_normalizer_sylow (hP.toSylow hPi)
  intro x hx
  have : x ∈ W ⊓ Subgroup.normalizer ((hP.toSylow hPi : Sylow 2 G) : Set G) := ⟨hx, hWN' hx⟩
  rw [h1] at this
  exact (IsPGroup.mem_toSylow hP hPi).1 this.2

variable {J V V₂ Z : Subgroup G} {e : ℕ}

theorem L3Local.weaklyClosed [Finite G] (h : L3Local G J V V₂ Z e) {t : G} (ht : t ∈ V)
    (ht1 : t ≠ 1) {g : G} (hg : conjSub V g ≤ Subgroup.centralizer ({t} : Set G)) :
    conjSub V g = V := by
  have hF : FusionData J V V₂ :=
    ⟨h.pgroup, h.odd_index, h.le, h.normalizes, h.normalizes₂, h.ne, h.abelian, h.sq, h.mem⟩
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Z = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    have h1 : Nat.card Z = 1 := by rw [this, Subgroup.card_bot]
    have h2 : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.three_le
    rw [h.card_Z] at h1
    omega
  have hzV : z ∈ V := h.Z_le hzZ
  obtain ⟨m, hmN, hmt⟩ := h.transitive t ht ht1 z hzV hz1
  set W' : Subgroup G := conjSub V (m * g) with hW'
  have hW'N : ∀ w ∈ W', w ∈ Subgroup.normalizer (Z : Set G) := by
    rintro w ⟨v, hv, hw⟩
    have hwv : w = m * g * v * (m * g)⁻¹ := hw.symm
    apply mem_normalizer_of_conjSub_eq
    apply h.ti
    have hc : t * (g * v * g⁻¹) = (g * v * g⁻¹) * t := by
      have := hg ⟨v, hv, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at this
      exact this t (Set.mem_singleton t)
    have hwz : w * z = z * w := by
      rw [hwv, ← hmt]
      calc m * g * v * (m * g)⁻¹ * (m * t * m⁻¹)
          = m * ((g * v * g⁻¹) * t) * m⁻¹ := by group
        _ = m * (t * (g * v * g⁻¹)) * m⁻¹ := by rw [hc]
        _ = m * t * m⁻¹ * (m * g * v * (m * g)⁻¹) := by group
    have hzw : z ∈ conjSub Z w := by
      have := conj_mem_conjSub w hzZ
      rwa [mul_inv_eq_iff_eq_mul.2 hwz] at this
    intro hbot
    have : z ∈ Z ⊓ conjSub Z w := ⟨hzZ, hzw⟩
    rw [hbot] at this
    exact hz1 (Subgroup.mem_bot.1 this)
  have hW'J : W' ≤ Subgroup.normalizer (J : Set G) :=
    fun w hw => mem_normalizer_of_conjSub_eq (h.normal_J w (hW'N w hw))
  have hW'2 : IsPGroup 2 W' := (h.pgroup.to_le h.le).map (MulAut.conj (m * g)).toMonoidHom
  have hW'le : W' ≤ J := le_of_normalizes_sylow h.pgroup h.odd_index hW'2 hW'J
  have hcard : Nat.card W' = Nat.card V := card_conjSub_eq V (m * g)
  rcases h.mem W' hW'le (commute_of_mem_conjSub h.abelian (m * g))
      (sq_of_mem_conjSub h.sq (m * g)) hcard with hV | hV₂
  ·
    have h1 : conjSub (conjSub V g) m = conjSub V m := by
      rw [← conjSub_mul]
      exact hV.trans (conjSub_of_mem_normalizer hmN).symm
    exact (conjSub_inj_iff m).1 h1
  · exact absurd hV₂ (hF.not_conj (m * g))

theorem L3Local.isWC [Finite G] (h : L3Local G J V V₂ Z e) : IsWC V := by
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (h.abelian a a.2 b b.2).eq⟩⟩, fun x hx => ?_⟩,
    fun t ht ht1 => ⟨?_, fun g hg => h.weaklyClosed ht ht1 hg⟩⟩
  · rw [pow_two]
    exact h.sq x hx
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (h.abelian t ht x hx).eq

end CFSG.CGT.PushingUpLit.A78
