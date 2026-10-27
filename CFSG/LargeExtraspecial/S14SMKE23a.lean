module

public import CFSG.LargeExtraspecial.S14SMKLift
public import CFSG.LargeExtraspecial.S14SMKDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.SmithE CFSG.F4.Native CFSG.LargeExtraspecial.SMod20
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] V}

theorem Phi_mul_apply {x y : S.M} (v : V) :
    Phi S φ (x * y) v = Phi S φ x (Phi S φ y v) := by
  rw [map_mul, LinearEquiv.mul_apply]

theorem mem_C8_of_cent2
    {t u : G} {htM : t ∈ S.M} {huM : u ∈ S.M} (ht0 : Phi S φ ⟨t, htM⟩ = tvEquiv 0)
    (hu1 : Phi S φ ⟨u, huM⟩ = tvEquiv 1) {q : G} (hq : q ∈ S.QG) (hqt : Commute q t)
    (hqu : Commute q u) : φ (S.cl q) ∈ C8 := by
  rw [mem_C8_iff]
  have hfix : ∀ {x : G} (hx : x ∈ S.M), Commute q x → Phi S φ ⟨x, hx⟩ (φ (S.cl q)) =
      φ (S.cl q) := by
    intro x hx hqx
    rw [Phi_cl ⟨x, hx⟩ hq]
    congr 2
    show x * q * x⁻¹ = q
    rw [← hqx.eq, mul_inv_cancel_right]
  exact ⟨by rw [← ht0]; exact hfix htM hqt, by rw [← hu1]; exact hfix huM hqu⟩

theorem exists_cent2_of_mem_C8
    (h34a : SmithE34a) [IsSimpleGroup G] (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G} (C : SMJ.Cfg S t u)
    (ht0 : Phi S φ ⟨t, C.htM⟩ = tvEquiv 0) (hu1 : Phi S φ ⟨u, C.huM⟩ = tvEquiv 1) {v : V}
    (hv : v ∈ C8) : ∃ q ∈ S.QG, Commute q t ∧ Commute q u ∧ φ (S.cl q) = v := by
  obtain ⟨hv0, hv1⟩ := (mem_C8_iff v).mp hv
  have hfix : ∀ {x : G} (hx : x ∈ S.M), Phi S φ ⟨x, hx⟩ v = v → φ.symm v ∈ S.fixQt x := by
    intro x hx h
    rw [S.fixQt_of_mem hx, mem_fixSpace]
    have := congrArg φ.symm h
    rw [Phi_apply, LinearEquiv.symm_apply_apply] at this
    exact this
  have h1 := hfix C.htM (by rw [ht0]; exact hv0)
  have h2 := hfix C.huM (by rw [hu1]; exact hv1)
  rw [SMJ.fixQt_eq_of_smithE34a h34a S hw hU C.ht C.htM C.htQ, S.mem_clSub_iff] at h1
  rw [SMJ.fixQt_eq_of_smithE34a h34a S hw hU C.hu C.huM C.huQ, S.mem_clSub_iff] at h2
  obtain ⟨q₁, hq₁, hq₁Q, hq₁v⟩ := h1
  obtain ⟨q₂, hq₂, hq₂Q, hq₂v⟩ := h2
  have hq₁t : Commute q₁ t := (mem_centralizer_singleton_iff.mp (mem_inf.mp hq₁).2)
  have hq₂u : Commute q₂ u := (mem_centralizer_singleton_iff.mp (mem_inf.mp hq₂).2)
  have hq₂t : Commute q₂ t := by
    rcases (S.cl_eq_cl_iff hq₁Q hq₂Q).mp (hq₁v.trans hq₂v.symm) with rfl | rfl
    · exact hq₁t
    · exact hq₁t.mul_left (S.z_comm C.htM).symm
  exact ⟨q₂, hq₂Q, hq₂t, hq₂u, by rw [hq₂v, LinearEquiv.apply_symm_apply]⟩

@[expose] def Lifts (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V)
    (t u : G) : Prop :=
  ∀ r ∈ c8Pts, ∃ y : S.M, IsConj S.z (y : G) ∧ (y : G) ∉ S.QG ∧ Commute (y : G) t ∧
    Commute (y : G) u ∧ Phi S φ y = tvEquiv r

theorem Phi_commute {x y : S.M} (h : Commute (x : G) (y : G)) :
    Commute (Phi S φ x) (Phi S φ y) := by
  have : x * y = y * x := Subtype.ext h.eq
  show Phi S φ x * Phi S φ y = Phi S φ y * Phi S φ x
  rw [← map_mul, this, map_mul]

theorem mem_QG_of_fix_C8
    (h4 : ∀ x : G, IsConj S.z x → ∀ hx : x ∈ S.M, x ∉ S.QG →
      ∃ k < 693, Phi S φ ⟨x, hx⟩ = tvEquiv k)
    {t u : G} {htM : t ∈ S.M} {huM : u ∈ S.M} (ht0 : Phi S φ ⟨t, htM⟩ = tvEquiv 0)
    (hu1 : Phi S φ ⟨u, huM⟩ = tvEquiv 1) (hL : Lifts S φ t u) {c : G} (hcM : c ∈ S.M)
    (hct : Commute c t) (hcu : Commute c u) (hfix : ∀ v ∈ C8, Phi S φ ⟨c, hcM⟩ v = v) :
    c ∈ S.QG := by
  set A := Phi S φ ⟨c, hcM⟩ with hA
  have hA0 : Commute A (tvEquiv 0) := by
    rw [← ht0]; exact Phi_commute (x := ⟨c, hcM⟩) (y := ⟨t, htM⟩) hct
  have hA1 : Commute A (tvEquiv 1) := by
    rw [← hu1]; exact Phi_commute (x := ⟨c, hcM⟩) (y := ⟨u, huM⟩) hcu
  have hAinv : ∀ v ∈ C8, A⁻¹ v = v := fun v hv => by
    conv_lhs => rw [← hfix v hv]
    exact A.symm_apply_apply v
  have hAr : ∀ r ∈ c8Pts, Commute A (tvEquiv r) := by
    intro r hr
    obtain ⟨hr693, hr0, hr1⟩ := commute_c8Pts hr
    obtain ⟨Y, hYz, hYQ, hYt, hYu, hYr⟩ := hL r hr
    set X : S.M := ⟨c, hcM⟩ * Y * ⟨c, hcM⟩⁻¹ with hX
    have hXz : IsConj S.z (X : G) := hYz.trans (isConj_iff.mpr ⟨c, by rw [hX]; push_cast; rfl⟩)
    have hXQ : (X : G) ∉ S.QG := fun h => hYQ (by
      have := conj_mem_QG_inv hcM h
      rwa [hX, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, show (⟨c, hcM⟩ : S.M) =
        (⟨c, hcM⟩ : S.M) from rfl, conj_conj] at this)
    obtain ⟨s, hs, hXs⟩ := h4 (X : G) hXz X.2 hXQ
    have hXA : Phi S φ X = A * tvEquiv r * A⁻¹ := by
      rw [hX, map_mul, map_mul, map_inv, hYr]
    have hXt : Commute (X : G) t := by
      rw [hX]; push_cast
      exact (hct.mul_left hYt).mul_left hct.inv_left
    have hXu : Commute (X : G) u := by
      rw [hX]; push_cast
      exact (hcu.mul_left hYu).mul_left hcu.inv_left
    have hs0 : Commute (tvEquiv s) (tvEquiv 0) := by
      rw [← hXs, ← ht0]; exact Phi_commute (x := X) (y := ⟨t, htM⟩) hXt
    have hs1 : Commute (tvEquiv s) (tvEquiv 1) := by
      rw [← hXs, ← hu1]; exact Phi_commute (x := X) (y := ⟨u, huM⟩) hXu
    have hsr : s = r := by
      refine eq_of_restr hs hs0 hs1 hr fun v hv => ?_
      have hrv : tvEquiv r v ∈ C8 := by
        obtain ⟨h0, h1⟩ := (mem_C8_iff v).mp hv
        refine (mem_C8_iff _).mpr ⟨?_, ?_⟩
        · rw [commute_apply hr0.symm, h0]
        · rw [commute_apply hr1.symm, h1]
      rw [← hXs, hXA, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hAinv v hv, hfix _ hrv]
    rw [hsr] at hXs
    have e : A * tvEquiv r * A⁻¹ = tvEquiv r := by rw [← hXA]; exact hXs
    show A * tvEquiv r = tvEquiv r * A
    calc A * tvEquiv r = A * tvEquiv r * A⁻¹ * A := by group
      _ = tvEquiv r * A := by rw [e]
  exact (Phi_eq_one_iff (φ := φ) _).mp (eq_one_of_commute A hAr hA0 hA1 hfix)

theorem single_mem_C8 : (Pi.single (0 : Fin 20) (1 : ZMod 2) : V) ∈ C8 := fun m hm => by
  have : m ≠ 0 := fun h => by rw [h] at hm; simp at hm
  simp [this]

theorem nontrivial_C8 : Nontrivial C8 :=
  ⟨⟨⟨_, single_mem_C8⟩, 0, fun h => by
    have := congrFun (congrArg Subtype.val h) 0
    simp at this⟩⟩

theorem clauses_std
    (h34a : SmithE34a) [IsSimpleGroup G] (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (h4 : ∀ x : G, IsConj S.z x → ∀ hx : x ∈ S.M, x ∉ S.QG →
      ∃ k < 693, Phi S φ ⟨x, hx⟩ = tvEquiv k)
    {t u : G} (C : SMJ.Cfg S t u) (ht0 : Phi S φ ⟨t, C.htM⟩ = tvEquiv 0)
    (hu1 : Phi S φ ⟨u, C.huM⟩ = tvEquiv 1) (hL : Lifts S φ t u) : Clauses S t u := by
  refine ⟨fun c hcM hct hcu hcq => ?_, fun P hPM hPc hPn hP2 => ?_,
    fun R hzR hRQ hRc hRn => ?_, ?_⟩
  ·
    refine mem_QG_of_fix_C8 h4 ht0 hu1 hL hcM hct hcu fun v hv => ?_
    obtain ⟨q, hq, hqt, hqu, rfl⟩ := exists_cent2_of_mem_C8 h34a hw hU C ht0 hu1 hv
    rw [Phi_cl ⟨c, hcM⟩ hq]
    congr 2
    show c * q * c⁻¹ = q
    rw [(hcq q hq hqt hqu).eq, mul_inv_cancel_right]
  ·
    set Pm : Subgroup S.M := P.comap S.M.subtype with hPm
    have hPm2 : IsPGroup 2 Pm := hP2.comap_of_injective _ Subtype.val_injective
    have hcomm : ∀ p : Pm, Commute (Phi S φ (p : S.M)) (tvEquiv 0) ∧
        Commute (Phi S φ (p : S.M)) (tvEquiv 1) := fun p => by
      obtain ⟨hpt, hpu⟩ := hPc _ p.2
      refine ⟨?_, ?_⟩
      · rw [← ht0]; exact Phi_commute (x := (p : S.M)) (y := ⟨t, C.htM⟩) hpt
      · rw [← hu1]; exact Phi_commute (x := (p : S.M)) (y := ⟨u, C.huM⟩) hpu
    have hpres : ∀ p : Pm, ∀ v ∈ C8, Phi S φ (p : S.M) v ∈ C8 := fun p v hv => by
      obtain ⟨hv0, hv1⟩ := (mem_C8_iff v).mp hv
      exact (mem_C8_iff _).mpr ⟨by rw [← commute_apply (hcomm p).1, hv0],
        by rw [← commute_apply (hcomm p).2, hv1]⟩
    let act : MulAction Pm C8 :=
      { smul := fun p v => ⟨Phi S φ (p : S.M) v, hpres p v v.2⟩
        one_smul := fun v => Subtype.ext (by
          show Phi S φ ((1 : Pm) : S.M) v = v
          rw [Subgroup.coe_one, map_one]
          rfl)
        mul_smul := fun p q v => Subtype.ext (by
          show Phi S φ ((p * q : Pm) : S.M) v = Phi S φ (p : S.M) (Phi S φ (q : S.M) v)
          rw [Subgroup.coe_mul, Phi_mul_apply]) }
    have : Nontrivial C8 := nontrivial_C8
    have hdvd : 2 ∣ Nat.card C8 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := C8)).ne'
    have h0 : (0 : C8) ∈ MulAction.fixedPoints Pm C8 := fun p => Subtype.ext (by
      show Phi S φ (p : S.M) 0 = 0
      exact map_zero _)
    obtain ⟨b, hb, hb0⟩ := hPm2.exists_fixed_point_of_prime_dvd_card_of_fixed_point C8 hdvd h0
    let N : Submodule (ZMod 2) V :=
      { carrier := {v | v ∈ C8 ∧ ∀ p : Pm, Phi S φ (p : S.M) v = v}
        add_mem' := fun ha hb => ⟨C8.add_mem ha.1 hb.1, fun p => by
          rw [map_add, ha.2 p, hb.2 p]⟩
        zero_mem' := ⟨C8.zero_mem, fun p => map_zero _⟩
        smul_mem' := fun c v hv => ⟨C8.smul_mem c hv.1, fun p => by rw [map_smul, hv.2 p]⟩ }
    have hNC8 : N ≤ C8 := fun v hv => hv.1
    have hNinv : ∀ r ∈ c8Pts, ∀ v ∈ N, tvEquiv r v ∈ N := by
      intro r hr v hv
      obtain ⟨hr693, hr0, hr1⟩ := commute_c8Pts hr
      obtain ⟨Y, -, -, hYt, hYu, hYr⟩ := hL r hr
      refine ⟨?_, fun p => ?_⟩
      · obtain ⟨h0, h1⟩ := (mem_C8_iff v).mp hv.1
        exact (mem_C8_iff _).mpr ⟨by rw [commute_apply hr0.symm, h0],
          by rw [commute_apply hr1.symm, h1]⟩
      ·
        have hp' : (Y : G)⁻¹ * ((p : S.M) : G) * (Y : G) ∈ P := by
          have := hPn ((Y : G)⁻¹) (S.M.inv_mem Y.2) hYt.inv_left hYu.inv_left _ p.2
          rwa [inv_inv] at this
        have e : Phi S φ (p : S.M) (Phi S φ Y v) =
            Phi S φ Y (Phi S φ (Y⁻¹ * (p : S.M) * Y) v) := by
          rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
          exact ((Phi S φ Y).apply_symm_apply _).symm
        rw [← hYr, e, hv.2 ⟨_, hp'⟩]
    rcases c8_irreducible N hNC8 hNinv with hbot | htop
    · exfalso
      apply hb0
      have hbN : (b : V) ∈ N := ⟨b.2, fun p => congrArg Subtype.val (hb p)⟩
      rw [hbot, Submodule.mem_bot] at hbN
      exact (Subtype.ext hbN).symm
    · intro p hp
      have hpM : p ∈ S.M := hPM hp
      obtain ⟨hpt, hpu⟩ := hPc p hp
      refine mem_QG_of_fix_C8 h4 ht0 hu1 hL hpM hpt hpu fun v hv => ?_
      have hvN : v ∈ N := by rw [htop]; exact hv
      exact hvN.2 ⟨⟨p, hpM⟩, hp⟩
  ·
    let N : Submodule (ZMod 2) V := (S.clSub R).map (φ : S.Qt →ₗ[ZMod 2] V)
    have hmem : ∀ {v : V}, v ∈ N ↔ ∃ q ∈ R, q ∈ S.QG ∧ φ (S.cl q) = v := fun {v} => by
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hw
        exact ⟨q, hq, hqQ, rfl⟩
      · rintro ⟨q, hq, hqQ, rfl⟩
        exact ⟨S.cl q, S.mem_clSub_iff.mpr ⟨q, hq, hqQ, rfl⟩, rfl⟩
    have hNC8 : N ≤ C8 := fun v hv => by
      obtain ⟨q, hq, hqQ, rfl⟩ := hmem.mp hv
      exact mem_C8_of_cent2 ht0 hu1 hqQ (hRc q hq).1 (hRc q hq).2
    have hNinv : ∀ r ∈ c8Pts, ∀ v ∈ N, tvEquiv r v ∈ N := by
      intro r hr v hv
      obtain ⟨Y, -, -, hYt, hYu, hYr⟩ := hL r hr
      obtain ⟨q, hq, hqQ, rfl⟩ := hmem.mp hv
      rw [← hYr, Phi_cl Y hqQ]
      exact hmem.mpr ⟨_, hRn _ Y.2 hYt hYu q hq, S.conj_mem_QG Y.2 hqQ, rfl⟩
    rcases c8_irreducible N hNC8 hNinv with hbot | htop
    · left
      refine le_antisymm (fun q hq => ?_) ((zpowers_le).mpr hzR)
      have hqN : φ (S.cl q) ∈ N := hmem.mpr ⟨q, hq, hRQ hq, rfl⟩
      rw [hbot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff,
        S.cl_eq_zero_iff (hRQ hq)] at hqN
      rcases hqN with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · right
      intro q hq hqt hqu
      have hqN : φ (S.cl q) ∈ N := by rw [htop]; exact mem_C8_of_cent2 ht0 hu1 hq hqt hqu
      obtain ⟨q', hq', hq'Q, he⟩ := hmem.mp hqN
      rcases (S.cl_eq_cl_iff hq'Q hq).mp (φ.injective he) with rfl | rfl
      · exact hq'
      · exact R.mul_mem hq' hzR
  ·
    obtain ⟨r, hr⟩ := exists_mem_c8Pts
    obtain ⟨Y, hYz, hYQ, hYt, hYu, -⟩ := hL r hr
    exact ⟨Y, hYz, Y.2, hYQ, hYt, hYu⟩

end CFSG.LargeExtraspecial.S14.SMK

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.SmithE CFSG.LargeExtraspecial.SMod20 SMK

theorem smithE23a_of_model
    (h : SmithEModel) :
    SmithE23a := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ h3
  have hM := smithE22Module_of_model h
  have h34a := smithE34a_of_module hM
  have h34b := smithE34b_of_module hM
  have h25 := smithE25_of hM
  have hLoc := smithU62LocalInput_of h34a h34b (smithE23_of hM) (smithE24_of hM) h25
  obtain ⟨φ, -, -, -, h4, h5⟩ := h G S hw hU
  have h4' : ∀ x : G, IsConj S.z x → ∀ hx : x ∈ S.M, x ∉ S.QG →
      ∃ k < 693, Phi S φ ⟨x, hx⟩ = tvEquiv k := by
    intro x hx hxM hxQ
    obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
    exact ⟨k, hk, (acts_iff hxM hk).mp hA⟩
  have h5' : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k := by
    intro k hk
    obtain ⟨m, hm, hA⟩ := h5 k hk
    exact ⟨⟨m, hm⟩, (acts_iff hm hk).mp hA⟩
  have C : SMJ.Cfg S t u := ⟨ht, hu, htM, huM, htQ, huQ, h3⟩
  obtain ⟨g, hg0, hg1⟩ := exists_conj_std h4' h5' C
  have hconjM : ∀ {x : G}, x ∈ S.M → (g : G) * x * (g : G)⁻¹ ∈ S.M := fun hx =>
    conj_mem_M g.2 hx
  have hconjQ : ∀ {x : G}, x ∉ S.QG → (g : G) * x * (g : G)⁻¹ ∉ S.QG := fun hx h => hx (by
    have := conj_mem_QG_inv g.2 h
    rwa [conj_conj] at this)
  have h3' : orderOf ((g : G) * t * (g : G)⁻¹ * ((g : G) * u * (g : G)⁻¹)) = 3 := by
    rw [show (g : G) * t * (g : G)⁻¹ * ((g : G) * u * (g : G)⁻¹) =
      MulAut.conj (g : G) (t * u) by rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact h3
  have C' : SMJ.Cfg S ((g : G) * t * (g : G)⁻¹) ((g : G) * u * (g : G)⁻¹) :=
    ⟨ht.trans (isConj_iff.mpr ⟨g, rfl⟩), hu.trans (isConj_iff.mpr ⟨g, rfl⟩), hconjM htM,
      hconjM huM, hconjQ htQ, hconjQ huQ, h3'⟩
  have ht0 : Phi S φ ⟨_, C'.htM⟩ = tvEquiv 0 := by
    rw [show (⟨_, C'.htM⟩ : S.M) = g * ⟨t, htM⟩ * g⁻¹ from rfl, map_mul, map_mul, map_inv, hg0]
  have hu1 : Phi S φ ⟨_, C'.huM⟩ = tvEquiv 1 := by
    rw [show (⟨_, C'.huM⟩ : S.M) = g * ⟨u, huM⟩ * g⁻¹ from rfl, map_mul, map_mul, map_inv, hg1]
  have hL : Lifts S φ ((g : G) * t * (g : G)⁻¹) ((g : G) * u * (g : G)⁻¹) := fun r hr =>
    exists_lift hM h34a h34b h25 hLoc hw hU h5' C' ht0 hu1 hr
  exact Clauses.of_conj g.2 (clauses_std h34a hw hU h4' C' ht0 hu1 hL)

end CFSG.LargeExtraspecial.S14
