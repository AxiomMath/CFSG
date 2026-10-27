module

public import CFSG.ClassicalInvolution.Asc77.AscT8Coset
public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.StronglyEmbedded.UniqueCosetE18
import CFSG.StronglyEmbedded.UniqueCosetFixedEng
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

section SixTwo

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mem_closure_pair_involutions {z b : G} (hz : z * z = 1) (hb : b * b = 1)
    (hzb : z * b = b * z) {w : G} (hw : w ∈ Subgroup.closure ({z, b} : Set G)) :
    w = 1 ∨ w = z ∨ w = b ∨ w = z * b := by
  have e1 : z * (z * b) = b := by rw [← mul_assoc, hz, one_mul]
  have e2 : b * z = z * b := hzb.symm
  have e3 : b * (z * b) = z := by rw [← mul_assoc, e2, mul_assoc, hb, mul_one]
  have e4 : z * b * z = b := by rw [mul_assoc, e2, e1]
  have e5 : z * b * b = z := by rw [mul_assoc, hb, mul_one]
  have e6 : z * b * (z * b) = 1 := by rw [← mul_assoc, e4, hb]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hw using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl <;> simp
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [hz, hb, e1, e2, e3, e4, e5, e6]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [hzi]
    · simp [hbi]
    · right; right; right
      rw [mul_inv_rev, hzi, hbi, e2]

omit [Finite G] in
theorem isConj_mul_of_aEmpty {K L : Subgroup G} (hAE : AEmpty Ω K) (hLs : L ∈ omegaStarNbr Ω K)
    (hLn : L ∉ omegaNbr Ω K) {z b : G} (hz : IsUniqueInvolution K z)
    (hb : IsUniqueInvolution L b) (hzb : z * b = b * z) (hne : b ≠ z) (hzb' : IsConj z b) :
    IsConj z (z * b) := by
  obtain ⟨y, hy, hyK⟩ := hAE L hLs hLn z b hz hb
  have hyz : y * z * y⁻¹ = b := by
    have := hz.conj y
    rw [hyK] at this
    exact (hb.eq this).symm
  have hZ : ∀ w ∈ Subgroup.closure ({z, b} : Set G), w = 1 ∨ w = z ∨ w = b ∨ w = z * b :=
    fun w hw => mem_closure_pair_involutions hz.sq hb.sq hzb hw
  have hbZ : b ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  have hzZ : z ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  by_contra hcon
  have hKfix : ∀ k ∈ K ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, b} : Set G) : Subgroup G) : Set G), k * b * k⁻¹ = b := by
    intro k hk
    by_contra hkb
    have hkz : k * z * k⁻¹ = z := hz.conj_eq (conjSub_eq_self_of_mem hk.1)
    have hkbZ : k * b * k⁻¹ ∈ Subgroup.closure ({z, b} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hk.2 b).mp hbZ
    rcases hZ _ hkbZ with h | h | h | h
    · exact hb.ne_one (by simpa using h)
    · apply hne
      calc b = k⁻¹ * (k * b * k⁻¹) * k := by group
        _ = k⁻¹ * z * k := by rw [h]
        _ = k⁻¹ * (k * z * k⁻¹) * k := by rw [hkz]
        _ = z := by group
    · exact hkb h
    · exact hcon (hzb'.trans (isConj_iff.mpr ⟨k, h⟩))
  have hLfix : ∀ l ∈ L ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, b} : Set G) : Subgroup G) : Set G), l * z * l⁻¹ = z := by
    intro l hl
    by_contra hlz
    have hlb : l * b * l⁻¹ = b := hb.conj_eq (conjSub_eq_self_of_mem hl.1)
    have hlzZ : l * z * l⁻¹ ∈ Subgroup.closure ({z, b} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hl.2 z).mp hzZ
    rcases hZ _ hlzZ with h | h | h | h
    · exact hz.ne_one (by simpa using h)
    · exact hlz h
    · apply hne
      calc b = l⁻¹ * (l * b * l⁻¹) * l := by group
        _ = l⁻¹ * b * l := by rw [hlb]
        _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [h]
        _ = z := by group
    · exact hcon (isConj_iff.mpr ⟨l, h⟩)
  have hcommk : ∀ (k x : G), k * x * k⁻¹ = x → x * k = k * x := by
    intro k x h
    calc x * k = (k * x * k⁻¹) * k := by rw [h]
      _ = k * x := by group
  have hyC : y ∈ Subgroup.centralizer ({z, b} : Set G) := by
    have hle : pairNormalizers K L z b ≤ Subgroup.centralizer ({z, b} : Set G) := by
      unfold pairNormalizers
      refine sup_le (fun k hk => ?_) (fun l hl => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro w (rfl | rfl)
        · exact hcommk k _ (hz.conj_eq (conjSub_eq_self_of_mem hk.1))
        · exact hcommk k _ (hKfix k hk)
      · rw [Subgroup.mem_centralizer_iff]
        rintro w (rfl | rfl)
        · exact hcommk l _ (hLfix l hl)
        · exact hcommk l _ (hb.conj_eq (conjSub_eq_self_of_mem hl.1))
    exact hle hy
  have h1 := (Subgroup.mem_centralizer_iff.mp hyC) z (by simp)
  apply hne
  rw [← hyz]
  calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [h1]
    _ = z := by group

theorem isConj_or_mem_omegaNbr {K : Subgroup G} (hs : AscStand p f Ω K)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z) {g : G}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Ω K := by
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hne hcomm ⊢
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  rw [← hLdef]
  have hLΩ : L ∈ Ω := hLdef ▸ hΩ.conjInvariant g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hbz : IsConj z b := isConj_iff.mpr ⟨g⁻¹, by rw [hbdef, inv_inv]⟩
  have hLK : L ≠ K := by
    intro h
    rcases hz.unique b (h ▸ hb.mem) hb.sq with h1 | h1
    · exact hb.ne_one h1
    · exact hne h1
  have hLtw : L ∉ twinSet Ω K := fun h => hLK (hnt L h)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hnt hz
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hb2 : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  have hbLC : Subgroup.zpowers b ≤ L ⊓ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hb.mem, hbC⟩
  obtain ⟨V, hV, hbV⟩ := IsSylow2In.exists_ge hb2 hbLC
  have h62 := l6_2 p f hp hq G Ω hΩ K hK z hz L hLΩ hLtw b hb V hV
    (hbV (Subgroup.mem_zpowers b))
  rcases h62 with ⟨-, h1⟩ | ⟨hVb, -, R', hR'Ω, hR'K, hVR', hsd⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, -⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hCz hbC)) h1
  · left
    have hR'syl : IsSylow2In R' K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hR'Ω hR'K
    have h8 := hΩ.eight_le_of_mem_RSet hp hR'Ω
    have hzR' : z ∈ R' := T3.mem_of_isPGroup hz hR'K hR'syl.2.1 (by omega)
    have hz' : IsUniqueInvolution R' z :=
      AscP1Nine3.uniqueInvolution_restrict hz hR'K hzR'
    have hbR' : b ∉ R' := by
      intro h
      rcases hz.unique b (hR'K h) hb.sq with h1 | h1
      · exact hb.ne_one h1
      · exact hne h1
    rw [hVb] at hVR' hsd
    obtain ⟨r, -, hr⟩ := AschTight.exists_conj_eq_mul_of_isSemidihedral hR'syl.2.1 hz' hb.sq hbR'
      (hVR' (Subgroup.mem_zpowers b)) hsd
    exact hbz.trans (isConj_iff.mpr ⟨r, hr⟩)
  · have hLs : L ∈ omegaStarNbr Ω K := ⟨hLΩ, hLK, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hω : L ∈ omegaNbr Ω K
    · exact Or.inr hω
    · exact Or.inl (isConj_mul_of_aEmpty (hs.aEmpty K hK) hLs hω hz hb hcomm hne hbz)
  · right
    exact ⟨hLΩ, hLK, V, hVR, hV.1.trans inf_le_left, (hV.1.trans inf_le_right).trans hCz⟩

end SixTwo

section Coset

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem fixesUniqueCoset_z {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset z (H274 Ω K z) := by
  have hzH : z ∈ H274 Ω K z :=
    sigmaNorm_le_H274 K z (normalizer_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
      (Subgroup.le_normalizer hs.hz.mem))
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzH (fun x hx => ?_)
  exact mem_H274_of_conj_mem_H274 hs hcomp hx

end Coset

end T8

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_4a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → FixesUniqueCoset (z * t) (T8.H274 Ω K z)

variable {p f}

theorem c27_4_of_steps (h2 : C27_2 p f) (h4a : C27_4a p f) : C27_4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hcomp : dComp Ω K = dstarComp Ω K := h2 G Ω K J S R T W z t hs hdisc
  by_contra hne
  have hH : T8.H274 Ω K z ≠ ⊤ := hne
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact h4a G Ω K (conjSub g⁻¹ K) S' R' T' W' z (g⁻¹ * z * g) hstd hdisc
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
    exact hKs inferInstance
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact CFSG.StronglyEmbedded.UniqueCoset.false_of_uniqueCoset_of_not_isSolvable hH hz2 h1 h2'
    hTs hTnab hTc (CFSG.StronglyEmbedded.UniqueCoset.le_centralizer_of_isUniqueInvolution hz) hKs

end CFSG.ClassicalInvolution.Asc77
