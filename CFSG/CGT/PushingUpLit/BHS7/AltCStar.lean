module

public import CFSG.CGT.PushingUpLit.BHS7.AltAct
public import CFSG.CGT.PushingUpLit.BHS7.OddCocycle
public import CFSG.CGT.PushingUpLit.BHS7.AltPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ} {m : ℕ}

abbrev AltAct.Y (A : AltAct G T E m) : Subgroup (Equiv.Perm (Fin (2 * m + 1))) :=
  ((baum T).subgroupOf (E ⊔ baum T)).map A.Φ

omit [Finite Γ] in
theorem AltAct.mem_Y_of_mem_baum (A : AltAct G T E m) {x : ↥(E ⊔ baum T)}
    (hx : (x : Γ) ∈ baum T) : A.Φ x ∈ A.Y :=
  ⟨x, hx, rfl⟩

theorem AltAct.mem_cStarIn_of_mem_normalizer (A : AltAct G T E m) (h : MinCex G T)
    (hE : IsBTBlock G T E) {g : ↥(E ⊔ baum T)}
    (hg : A.Φ g ∈ Subgroup.normalizer (A.Y : Set (Equiv.Perm (Fin (2 * m + 1))))) :
    (g : Γ) ∈ cStarIn G T := by
  have hG := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.2.1.to_le inf_le_left
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hEG : E ≤ G := hE.le
  have hHG : E ⊔ baum T ≤ G := sup_le hEG ((inf_le_left : baum T ≤ T).trans hT2.1)
  set P : Subgroup Γ := (A.Y.comap A.Φ).map (E ⊔ baum T).subtype with hP
  have hPmem : ∀ x : Γ, x ∈ P ↔ ∃ hx : x ∈ E ⊔ baum T, A.Φ ⟨x, hx⟩ ∈ A.Y := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, hy, rfl⟩
  have hP2 : IsPGroup 2 ↥P := by
    intro x
    obtain ⟨hxH, hxY⟩ := (hPmem x).mp x.2
    obtain ⟨y, hy, hyx⟩ := hxY
    obtain ⟨j, hj⟩ := hT2.2.1 ⟨(y : Γ), (inf_le_left : baum T ≤ T) hy⟩
    have hj' : (y : Γ) ^ (2 ^ j) = 1 := by simpa using congrArg (fun z : ↥T => (z : Γ)) hj
    have h1 : A.Φ (⟨(x : Γ), hxH⟩ ^ (2 ^ j)) = 1 := by
      rw [map_pow, ← hyx, ← map_pow]
      have : y ^ (2 ^ j) = 1 := Subtype.ext hj'
      rw [this, map_one]
    have h2 := (A.ker_iff _).mp h1
    obtain ⟨i, hi⟩ := exists_pow_two_eq_one_of_centralizes hchar hE.elemAbelian.1 hB2 hBE
      (pow_mem hxH _) (by simpa using h2)
    refine ⟨j + i, Subtype.ext ?_⟩
    show (x : Γ) ^ (2 ^ (j + i)) = 1
    rw [pow_add, pow_mul]
    exact hi
  have hPG : P ≤ G := fun x hx => hHG ((hPmem x).mp hx).1
  have hBP : baum T ≤ P := fun b hb =>
    (hPmem b).mpr ⟨(le_sup_right : baum T ≤ E ⊔ baum T) hb, A.mem_Y_of_mem_baum hb⟩
  have hconj : ∀ g' : ↥(E ⊔ baum T),
      A.Φ g' ∈ Subgroup.normalizer (A.Y : Set (Equiv.Perm (Fin (2 * m + 1)))) →
      ∀ x ∈ P, (g' : Γ) * x * (g' : Γ)⁻¹ ∈ P := by
    intro g' hg' x hx
    obtain ⟨hxH, hxY⟩ := (hPmem x).mp hx
    have hmem : (g' : Γ) * x * (g' : Γ)⁻¹ ∈ E ⊔ baum T :=
      (E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem g'.2 hxH) ((E ⊔ baum T).inv_mem g'.2)
    refine (hPmem _).mpr ⟨hmem, ?_⟩
    have e : (⟨(g' : Γ) * x * (g' : Γ)⁻¹, hmem⟩ : ↥(E ⊔ baum T)) = g' * ⟨x, hxH⟩ * g'⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg' _).mp hxY
  have hgP : (g : Γ) ∈ Subgroup.normalizer (P : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj g hg x hx, fun hx => ?_⟩
    have hg' : A.Φ g⁻¹ ∈ Subgroup.normalizer (A.Y : Set (Equiv.Perm (Fin (2 * m + 1)))) := by
      rw [map_inv]
      exact (Subgroup.normalizer _).inv_mem hg
    have := hconj g⁻¹ hg' _ hx
    have e : ((g⁻¹ : ↥(E ⊔ baum T)) : Γ) * ((g : Γ) * x * (g : Γ)⁻¹) *
        ((g⁻¹ : ↥(E ⊔ baum T)) : Γ)⁻¹ = x := by
      simp [mul_assoc]
    rwa [e] at this
  exact inf_normalizer_baum_le_cStarIn hb0
    ⟨hHG g.2, mem_normalizer_baum_of_pGroup hT2 hP2 hPG hBP (hHG g.2) hgP⟩

omit [Finite Γ] in
theorem AltAct.eq_one_of_centralizes (A : AltAct G T E m) (hm : 1 ≤ m) {w : Γ}
    (hw : w ∈ pCoreOf 2 E) (hfix : ∀ e ∈ E, e * w * e⁻¹ = w) : w = 1 := by
  have hn : Odd (2 * m + 1) := odd_two_mul_add_one m
  have h3 : 3 ≤ 2 * m + 1 := by omega
  have hu : A.β ⟨w, hw⟩ = 1 := by
    refine eq_one_of_fixed_alternatingGroup hn h3 fun a ha => ?_
    obtain ⟨x, hxE, hxa⟩ := A.exists_of_alt a ha
    have h1 := A.β_compat x ⟨w, hw⟩ ⟨w, hw⟩ (hfix x hxE).symm
    rw [hxa] at h1
    exact h1.symm
  have h2 : (⟨w, hw⟩ : ↥(pCoreOf 2 E)) = 1 := A.β_inj (hu.trans A.β_one.symm)
  exact congrArg Subtype.val h2

theorem AltAct.exists_centralized_mul (A : AltAct G T E m) (hm : 1 ≤ m) (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) (hS : IsSylowTwoOf (T ⊓ E) E) {z : Γ}
    (hz : z ∈ omegaOneCenterOf T) :
    ∃ w ∈ pCoreOf 2 E, ∀ h ∈ E ⊔ baum T, h * (w * z) * h⁻¹ = w * z := by
  classical
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hWab : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x := hE.elemAbelian.1
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hBW : baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hWT : pCoreOf 2 E ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hzc : z ∈ centerOf T := C1GN.omegaOneCenterOf_le_centerOf T hz
  have hzT : z ∈ T := (Subgroup.mem_inf.mp hzc).1
  have hzcomm : ∀ y ∈ T, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzc).2 y hy
  have hzB : z ∈ baum T := C1GN.omegaOneCenterOf_le_baum T hz
  have hzH : z ∈ E ⊔ baum T := (le_sup_right : baum T ≤ E ⊔ baum T) hzB
  have hzW : z ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => hzcomm w (hWT hw)
  have hΦz : A.Φ ⟨z, hzH⟩ = 1 := (A.ker_iff _).mpr hzW
  have hcW : ∀ e : ↥E, (e : Γ) * z * (e : Γ)⁻¹ * z⁻¹ ∈ pCoreOf 2 E := by
    intro e
    have heH : (e : Γ) ∈ E ⊔ baum T := (le_sup_left : E ≤ E ⊔ baum T) e.2
    have hzE : z * (e : Γ)⁻¹ * z⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hBE hzB) _).mp (E.inv_mem e.2)
    have h1 : (e : Γ) * z * (e : Γ)⁻¹ * z⁻¹ ∈ E := by
      have := E.mul_mem e.2 hzE
      simpa [mul_assoc] using this
    have hmemH : (e : Γ) * z * (e : Γ)⁻¹ * z⁻¹ ∈ E ⊔ baum T :=
      (E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem heH hzH)
        ((E ⊔ baum T).inv_mem heH)) ((E ⊔ baum T).inv_mem hzH)
    have hΦ1 : A.Φ ⟨(e : Γ) * z * (e : Γ)⁻¹ * z⁻¹, hmemH⟩ = 1 := by
      have e1 : (⟨(e : Γ) * z * (e : Γ)⁻¹ * z⁻¹, hmemH⟩ : ↥(E ⊔ baum T)) =
          ⟨e, heH⟩ * ⟨z, hzH⟩ * ⟨e, heH⟩⁻¹ * ⟨z, hzH⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hΦz]
      simp
    have hC := (A.ker_iff _).mp hΦ1
    have hmem : (e : Γ) * z * (e : Γ)⁻¹ * z⁻¹ ∈
        E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := Subgroup.mem_inf.mpr ⟨h1, hC⟩
    rwa [inf_centralizer_pCoreOf_eq hchar hWab] at hmem
  let ρ : ↥E →* MulAut ↥(pCoreOf 2 E) := actOn (pCoreOf 2 E) E hEW
  let c : ↥E → ↥(pCoreOf 2 E) := fun e => ⟨(e : Γ) * z * (e : Γ)⁻¹ * z⁻¹, hcW e⟩
  have hc : ∀ a b : ↥E, c (a * b) = ρ a (c b) * c a := by
    intro a b
    apply Subtype.ext
    show (a : Γ) * (b : Γ) * z * ((a : Γ) * (b : Γ))⁻¹ * z⁻¹ =
      (a : Γ) * ((b : Γ) * z * (b : Γ)⁻¹ * z⁻¹) * (a : Γ)⁻¹ * ((a : Γ) * z * (a : Γ)⁻¹ * z⁻¹)
    group
  have hcS : ∀ s ∈ (T ⊓ E).subgroupOf E, c s = 1 := by
    intro s hs
    have hsT : (s : Γ) ∈ T := (Subgroup.mem_subgroupOf.mp hs).1
    apply Subtype.ext
    show (s : Γ) * z * (s : Γ)⁻¹ * z⁻¹ = 1
    rw [hzcomm _ hsT]
    group
  have hM2 : ∀ m : ↥(pCoreOf 2 E), m * m = 1 := fun m => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hE.elemAbelian.2 m m.2)
  have hMc : ∀ a b : ↥(pCoreOf 2 E), a * b = b * a := fun a b =>
    Subtype.ext (hWab a a.2 b b.2)
  obtain ⟨m₀, hm₀⟩ := exists_coboundary_of_odd_index hMc hM2 ρ c hc _ hcS hS.2.2
  set w : Γ := (m₀ : Γ) with hw
  have hwW : w ∈ pCoreOf 2 E := m₀.2
  have hfixE : ∀ e ∈ E, e * (w * z) * e⁻¹ = w * z := by
    intro e he
    have h1 := congrArg Subtype.val (hm₀ ⟨e, he⟩)
    have h2 : ((ρ ⟨e, he⟩ m₀ : ↥(pCoreOf 2 E)) : Γ) = e * w * e⁻¹ :=
      actOn_apply_coe hEW ⟨e, he⟩ m₀
    have hew : e * w * e⁻¹ ∈ pCoreOf 2 E := h2 ▸ (ρ ⟨e, he⟩ m₀).2
    have h3 : e * z * e⁻¹ * z⁻¹ = w * (e * w * e⁻¹)⁻¹ := by
      have := h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2] at this
      exact this
    have h4 : e * z * e⁻¹ = w * (e * w * e⁻¹)⁻¹ * z := by
      rw [← h3]
      group
    calc e * (w * z) * e⁻¹ = (e * w * e⁻¹) * (e * z * e⁻¹) := by group
      _ = (e * w * e⁻¹) * (w * (e * w * e⁻¹)⁻¹ * z) := by rw [h4]
      _ = ((e * w * e⁻¹) * w * (e * w * e⁻¹)⁻¹) * z := by group
      _ = (w * (e * w * e⁻¹) * (e * w * e⁻¹)⁻¹) * z := by rw [hWab _ hew w hwW]
      _ = w * z := by group
  have hfixB : ∀ b ∈ baum T, b * (w * z) * b⁻¹ = w * z := by
    intro b hb
    have hbT : b ∈ T := (inf_le_left : baum T ≤ T) hb
    have hbz : b * z * b⁻¹ = z := by
      rw [hzcomm b hbT]
      group
    have hw'W : b * w * b⁻¹ ∈ pCoreOf 2 E := (Subgroup.mem_normalizer_iff.mp (hBW hb) w).mp hwW
    have hz₁ : ∀ e ∈ E, e * (b * (w * z) * b⁻¹) * e⁻¹ = b * (w * z) * b⁻¹ := by
      intro e he
      have hbe : b⁻¹ * e * b ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (E : Set Γ)).inv_mem
          (hBE hb)) e).mp he
        simpa using this
      have := hfixE _ hbe
      calc e * (b * (w * z) * b⁻¹) * e⁻¹
          = b * ((b⁻¹ * e * b) * (w * z) * (b⁻¹ * e * b)⁻¹) * b⁻¹ := by group
        _ = b * (w * z) * b⁻¹ := by rw [this]
    have hu : (b * w * b⁻¹) * w⁻¹ ∈ pCoreOf 2 E :=
      (pCoreOf 2 E).mul_mem hw'W ((pCoreOf 2 E).inv_mem hwW)
    have hu1 : ((b * w * b⁻¹) * w⁻¹) = (b * (w * z) * b⁻¹) * (w * z)⁻¹ := by
      calc (b * w * b⁻¹) * w⁻¹ = (b * w * b⁻¹) * (b * z * b⁻¹) * (w * z)⁻¹ := by
            rw [hbz]
            group
        _ = (b * (w * z) * b⁻¹) * (w * z)⁻¹ := by group
    have hu2 : (b * w * b⁻¹) * w⁻¹ = 1 := by
      refine A.eq_one_of_centralizes hm hu fun e he => ?_
      rw [hu1]
      have h1 := hz₁ e he
      have h2 := hfixE e he
      calc e * ((b * (w * z) * b⁻¹) * (w * z)⁻¹) * e⁻¹
          = (e * (b * (w * z) * b⁻¹) * e⁻¹) * (e * (w * z) * e⁻¹)⁻¹ := by group
        _ = (b * (w * z) * b⁻¹) * (w * z)⁻¹ := by rw [h1, h2]
    have hbw : b * w * b⁻¹ = w := mul_inv_eq_one.mp hu2
    calc b * (w * z) * b⁻¹ = (b * w * b⁻¹) * (b * z * b⁻¹) := by group
      _ = w * z := by rw [hbw, hbz]
  refine ⟨w, hwW, fun h hh => ?_⟩
  have hle : E ⊔ baum T ≤ Subgroup.centralizer ({w * z} : Set Γ) := by
    refine sup_le (fun e he => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have := hfixE e he
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have := hfixB b hb
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have h1 := Subgroup.mem_centralizer_iff.mp (hle hh) (w * z) (Set.mem_singleton _)
  exact mul_inv_eq_iff_eq_mul.mpr h1.symm

theorem AltAct.mem_centralizer_of_fixes (A : AltAct G T E m) (hm : 1 ≤ m) (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) (hS : IsSylowTwoOf (T ⊓ E) E)
    {g : ↥(E ⊔ baum T)}
    (hfix : ∀ u : ↥(coreMod (2 * m + 1)),
      (∀ t : ↥(E ⊔ baum T), (t : Γ) ∈ T → coreAct (2 * m + 1) (A.Φ t) u = u) →
        coreAct (2 * m + 1) (A.Φ g) u = u) :
    (g : Γ) ∈ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) := by
  classical
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨w, hwW, hwc⟩ := A.exists_centralized_mul hm hG hT hE hS hz
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hBW : baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hHW : E ⊔ baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := sup_le hEW hBW
  have hzc : z ∈ centerOf T := C1GN.omegaOneCenterOf_le_centerOf T hz
  have hzcomm : ∀ y ∈ T, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzc).2 y hy
  have hwt : ∀ t : ↥(E ⊔ baum T), (t : Γ) ∈ T → (t : Γ) * w * (t : Γ)⁻¹ = w := by
    intro t ht
    have h1 := hwc t t.2
    have h2 : (t : Γ) * z * (t : Γ)⁻¹ = z := by
      rw [hzcomm _ ht]
      group
    calc (t : Γ) * w * (t : Γ)⁻¹
        = ((t : Γ) * (w * z) * (t : Γ)⁻¹) * ((t : Γ) * z * (t : Γ)⁻¹)⁻¹ := by group
      _ = (w * z) * z⁻¹ := by rw [h1, h2]
      _ = w := by group
  have hβ : ∀ t : ↥(E ⊔ baum T), (t : Γ) ∈ T →
      coreAct (2 * m + 1) (A.Φ t) (A.β ⟨w, hwW⟩) = A.β ⟨w, hwW⟩ := fun t ht =>
    (A.β_compat t ⟨w, hwW⟩ ⟨w, hwW⟩ (hwt t ht).symm).symm
  have hgβ := hfix (A.β ⟨w, hwW⟩) hβ
  have hgw : (g : Γ) * w * (g : Γ)⁻¹ = w := by
    have hmem : (g : Γ) * w * (g : Γ)⁻¹ ∈ pCoreOf 2 E :=
      (Subgroup.mem_normalizer_iff.mp (hHW g.2) w).mp hwW
    have h1 := A.β_compat g ⟨w, hwW⟩ ⟨_, hmem⟩ rfl
    rw [hgβ] at h1
    exact congrArg Subtype.val (A.β_inj h1)
  have h3 := hwc g g.2
  have h4 : (g : Γ) * z * (g : Γ)⁻¹ = z := by
    calc (g : Γ) * z * (g : Γ)⁻¹
        = ((g : Γ) * w * (g : Γ)⁻¹)⁻¹ * ((g : Γ) * (w * z) * (g : Γ)⁻¹) := by group
      _ = w⁻¹ * (w * z) := by rw [hgw, h3]
      _ = z := by group
  exact (mul_inv_eq_iff_eq_mul.mp h4).symm

end CFSG.CGT.PushingUpLit.BHS7
