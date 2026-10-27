module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7C

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rLayer_le_centralizer (x : G) : rLayer Ω x ≤ Subgroup.centralizer ({x} : Set G) := by
  unfold rLayer
  exact iSup₂_le fun _ _ => iSup_le fun h => h

theorem rLayerSub_le_centralizer (V : Subgroup G) :
    rLayerSub Ω V ≤ Subgroup.centralizer (V : Set G) := by
  unfold rLayerSub
  exact iSup₂_le fun _ _ => iSup_le fun h => h

theorem le_rLayer {x : G} {R : Subgroup G} (hR : R ∈ RSet Ω)
    (hRx : R ≤ Subgroup.centralizer ({x} : Set G)) : R ≤ rLayer Ω x := by
  unfold rLayer
  exact le_iSup₂_of_le R hR (le_iSup_of_le hRx le_rfl)

theorem le_rLayerSub {V R : Subgroup G} (hR : R ∈ RSet Ω)
    (hRV : R ≤ Subgroup.centralizer (V : Set G)) : R ≤ rLayerSub Ω V := by
  unfold rLayerSub
  exact le_iSup₂_of_le R hR (le_iSup_of_le hRV le_rfl)

theorem isPGroup_of_mem_RSet {R : Subgroup G} (hR : R ∈ RSet Ω) : IsPGroup 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, -, P, rfl⟩ := hR
  exact P.isPGroup'.map _

theorem mem_normalizer_rLayer (hΩ : HypOmegaGen Ω) {x g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    g ∈ Subgroup.normalizer (rLayer Ω x : Set G) := by
  have hE := conjSub_rLayer_eq hΩ hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hE]
    exact conj_mem_conjSub hh
  · intro hh
    rw [← hE, mem_conjSub_iff] at hh
    simpa [mul_assoc] using hh

theorem conj_mem_oddCoreOf_rLayer (hΩ : HypOmegaGen Ω) {x g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) {o : G} (ho : o ∈ oddCoreOf (rLayer Ω x)) :
    g * o * g⁻¹ ∈ oddCoreOf (rLayer Ω x) :=
  mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_rLayer hΩ hg) ho

theorem rLayer_le_cover (hΩ : HypOmegaGen Ω) {x : G} {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set G))
    (hVE : ∀ v ∈ V, ∀ a ∈ rLayer Ω x, v * a * v⁻¹ * a⁻¹ ∈ oddCoreOf (rLayer Ω x)) :
    rLayer Ω x ≤ oddCoreOf (rLayer Ω x) ⊔ (rLayer Ω x ⊓ rLayerSub Ω V) := by
  set E := rLayer Ω x with hEdef
  set O := oddCoreOf E with hOdef
  have hOE : O ≤ E := oddCoreOf_le_self E
  have hOodd : Odd (Nat.card O) := odd_natCard_oddCoreOf E
  have key : ∀ R ∈ RSet Ω, R ≤ Subgroup.centralizer ({x} : Set G) →
      R ≤ O ⊔ (E ⊓ rLayerSub Ω V) := by
    intro R hR hRx
    have hRE : R ≤ E := le_rLayer hR hRx
    have hR2 : IsPGroup 2 R := isPGroup_of_mem_RSet hR
    have hRN : R ≤ Subgroup.normalizer (O : Set G) :=
      hRE.trans (Sec7.le_normalizer_oddCoreOf E)
    set M := O ⊔ R with hMdef
    have hMV : ∀ v ∈ V, ∀ m ∈ M, v * m * v⁻¹ ∈ M := by
      intro v hv
      have hle : M ≤ M.comap (MulAut.conj v).toMonoidHom := by
        refine sup_le (fun o ho => ?_) (fun r hr => ?_)
        · rw [Subgroup.mem_comap]
          exact Subgroup.mem_sup_left (conj_mem_oddCoreOf_rLayer hΩ (hVx hv) ho)
        · rw [Subgroup.mem_comap]
          show v * r * v⁻¹ ∈ M
          have h1 : v * r * v⁻¹ * r⁻¹ ∈ M := Subgroup.mem_sup_left (hVE v hv r (hRE hr))
          have h2 := M.mul_mem h1 (Subgroup.mem_sup_right hr)
          simpa [mul_assoc] using h2
      intro m hm
      exact hle hm
    have hVNM : V ≤ Subgroup.normalizer (M : Set G) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hMV v hv h, fun hh => ?_⟩
      have := hMV v⁻¹ (V.inv_mem hv) _ hh
      simpa [mul_assoc] using this
    have hHN : M ⊔ V ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hVNM
    obtain ⟨T, hT, hVT⟩ := IsSylow2In.exists_ge hV2 (le_sup_right : V ≤ M ⊔ V)
    have hTM : IsSylow2In (T ⊓ M) M :=
      Asc77.isSylow2In_inf_of_le_normalizer hT le_sup_left hHN
    obtain ⟨a, haM, hRa⟩ := Asc77.exists_conj_of_isSylow2In hTM hR2 (le_sup_right : R ≤ M)
    have ha' : a ∈ ((R ⊔ O : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact haM
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN] at ha'
    obtain ⟨r, hr, o, ho, rfl⟩ := ha'
    have hconj : ∀ y ∈ R, o⁻¹ * y * o ∈ T := by
      intro y hy
      have hy' : r * y * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hy) (R.inv_mem hr)
      have h1 := hRa hy'
      rw [mem_conjSub_iff] at h1
      have h2 : (r * o)⁻¹ * (r * y * r⁻¹) * (r * o) = o⁻¹ * y * o := by group
      rw [h2] at h1
      exact h1.1
    have hoE : o ∈ E := hOE ho
    have hR₀ : conjSub o⁻¹ R ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR o⁻¹
    have hR₀C : conjSub o⁻¹ R ≤ Subgroup.centralizer (V : Set G) := by
      intro z hz
      rw [mem_conjSub_iff, inv_inv] at hz
      have hzeq : z = o⁻¹ * (o * z * o⁻¹) * o := by group
      have hzT : z ∈ T := by rw [hzeq]; exact hconj _ hz
      have hzE : z ∈ E := by
        rw [hzeq]
        exact E.mul_mem (E.mul_mem (E.inv_mem hoE) (hRE hz)) hoE
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hcO := hVE v hv z hzE
      have hvT : v ∈ T := hVT hv
      have hcT : v * z * v⁻¹ * z⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem hvT hzT) (T.inv_mem hvT)) (T.inv_mem hzT)
      have h1 := Sec13.L94T.eq_one_of_isPGroup_of_odd hT.2.1 hOodd hcT hcO
      have h2 : v * z = z * v := by
        have := congrArg (· * (z * v)) h1
        simpa [mul_assoc] using this
      exact h2
    have hR₀E : conjSub o⁻¹ R ≤ E := by
      intro z hz
      rw [mem_conjSub_iff, inv_inv] at hz
      have hzeq : z = o⁻¹ * (o * z * o⁻¹) * o := by group
      rw [hzeq]
      exact E.mul_mem (E.mul_mem (E.inv_mem hoE) (hRE hz)) hoE
    have hR₀Y : conjSub o⁻¹ R ≤ E ⊓ rLayerSub Ω V := le_inf hR₀E (le_rLayerSub hR₀ hR₀C)
    intro y hy
    have hmid : o⁻¹ * y * o ∈ conjSub o⁻¹ R := by
      rw [mem_conjSub_iff, inv_inv]
      simpa [mul_assoc] using hy
    have hyeq : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
    rw [hyeq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
      (Subgroup.mem_sup_right (hR₀Y hmid))) (Subgroup.mem_sup_left (O.inv_mem ho))
  calc E = ⨆ R ∈ RSet Ω, ⨆ (_ : R ≤ Subgroup.centralizer ({x} : Set G)), R := rfl
    _ ≤ _ := iSup₂_le fun R hR => iSup_le fun hRx => key R hR hRx

theorem comm_mem_of_cover (hΩ : HypOmegaGen Ω) {x : G} {V : Subgroup G}
    (hVx : V ≤ Subgroup.centralizer ({x} : Set G))
    (hcov : rLayer Ω x ≤ oddCoreOf (rLayer Ω x) ⊔ (rLayer Ω x ⊓ rLayerSub Ω V)) :
    ∀ v ∈ V, ∀ a ∈ rLayer Ω x, v * a * v⁻¹ * a⁻¹ ∈ oddCoreOf (rLayer Ω x) := by
  intro v hv a ha
  have hBN : rLayer Ω x ⊓ rLayerSub Ω V ≤ Subgroup.normalizer (oddCoreOf (rLayer Ω x) : Set G) :=
    inf_le_left.trans (Sec7.le_normalizer_oddCoreOf _)
  have ha' : a ∈ ((oddCoreOf (rLayer Ω x) ⊔ (rLayer Ω x ⊓ rLayerSub Ω V) : Subgroup G) : Set G) :=
    hcov ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at ha'
  obtain ⟨o, ho, b, hb, rfl⟩ := ha'
  have hvb : v * b = b * v := by
    have := (Subgroup.mem_centralizer_iff.mp (rLayerSub_le_centralizer V hb.2)) v hv
    exact this
  have hbv : b * v⁻¹ = v⁻¹ * b := by
    have := congrArg (fun w => v⁻¹ * w * v⁻¹) hvb
    simpa [mul_assoc] using this
  have h1 : v * (o * b) * v⁻¹ * (o * b)⁻¹ = (v * o * v⁻¹) * o⁻¹ := by
    calc v * (o * b) * v⁻¹ * (o * b)⁻¹ = v * o * (b * v⁻¹) * b⁻¹ * o⁻¹ := by group
      _ = v * o * (v⁻¹ * b) * b⁻¹ * o⁻¹ := by rw [hbv]
      _ = (v * o * v⁻¹) * o⁻¹ := by group
  rw [h1]
  exact Subgroup.mul_mem _ (conj_mem_oddCoreOf_rLayer hΩ (hVx hv) ho) (Subgroup.inv_mem _ ho)

theorem mem_rLayerSub_of_cover {x : G} {V : Subgroup G}
    (hcov : rLayer Ω x ≤ oddCoreOf (rLayer Ω x) ⊔ (rLayer Ω x ⊓ rLayerSub Ω V))
    (hx : x ∈ rLayer Ω x) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ rLayerSub Ω V := by
  obtain ⟨o, ho, h⟩ := exists_oddCore_conj_le hcov hx2 (Subgroup.zpowers_le.mpr hx)
  have h1 := h x (Subgroup.mem_zpowers x)
  have hoC := rLayer_le_centralizer (Ω := Ω) x (oddCoreOf_le_self _ ho)
  rw [Subgroup.mem_centralizer_singleton_iff] at hoC
  have h2 : o⁻¹ * x * o = x := by
    rw [mul_assoc, ← hoC]; group
  rwa [h2] at h1

end F7C

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
