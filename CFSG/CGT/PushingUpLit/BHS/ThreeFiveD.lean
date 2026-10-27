module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveC
public import CFSG.CGT.PushingUpLit.BHS.SecHom
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman CFSG.RankThree.PartOne CFSG.Open
  CFSG.LieType.BorelTits

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

theorem stab_wMod (ρ : Γ →* MulAut V) (T : Subgroup Γ) (g : Γ) :
    ρ g ∈ stabSub (wMod ρ T) := by
  intro u
  refine ⟨fun hu => ?_, fun hu => wMod_inv ρ T g hu⟩
  have := wMod_inv ρ T g⁻¹ hu
  simpa [← MulAut.mul_apply, ← map_mul] using this

theorem stab_fixV_range (ρ : Γ →* MulAut V) (g : Γ) : ρ g ∈ stabSub (fixV ρ.range) := by
  intro u
  have hfix : ∀ y ∈ fixV ρ.range, ∀ g : Γ, ρ g y = y := fun y hy g => hy _ ⟨g, rfl⟩
  refine ⟨fun hu => ?_, fun hu => by rw [hfix u hu g]; exact hu⟩
  have e : ρ g⁻¹ (ρ g u) = u := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have h1 := hfix _ hu g⁻¹
  rw [e] at h1
  have : u ∈ fixV ρ.range := by
    rw [h1]
    exact hu
  exact this

@[expose] noncomputable def secF (ρ : Γ →* MulAut V) (T : Subgroup Γ) :
    Γ →* MulAut (Sec (wMod ρ T) (fixV ρ.range)) :=
  secAct ρ (wMod ρ T) (fixV ρ.range) (stab_wMod ρ T) (stab_fixV_range ρ)

theorem secF_eq_one_iff (ρ : Γ →* MulAut V) (T : Subgroup Γ) (g : Γ) :
    secF ρ T g = 1 ↔ ∀ w ∈ wMod ρ T, ρ g w * w⁻¹ ∈ fixV ρ.range :=
  secAct_eq_one_iff ρ _ _ (stab_wMod ρ T) (stab_fixV_range ρ) g

theorem secF_mk (ρ : Γ →* MulAut V) (T : Subgroup Γ) (g : Γ) (w : ↥(wMod ρ T)) :
    secF ρ T g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨ρ g (w : V), wMod_inv ρ T g w.2⟩ : ↥(wMod ρ T)) := rfl

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

omit h in
theorem normalizer_cenW : ⊤ ≤ Subgroup.normalizer ((cenMod ρ (wMod ρ T) : Subgroup Γ) : Set Γ) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => conj_mem_cenMod (wMod_inv ρ T) hg x
  · intro hg
    have := conj_mem_cenMod (wMod_inv ρ T) hg x⁻¹
    simpa [mul_assoc] using this

omit h in
theorem cenW_le_ker : cenMod ρ (wMod ρ T) ≤ (secF ρ T).ker := by
  intro g hg
  rw [MonoidHom.mem_ker, secF_eq_one_iff]
  intro w hw
  rw [mem_cenMod.1 hg w hw, mul_inv_cancel]
  exact (fixV ρ.range).one_mem

theorem sq_mem_cenW {g : Γ} (hg : secF ρ T g = 1) : g ^ 2 ∈ cenMod ρ (wMod ρ T) := by
  rw [secF_eq_one_iff] at hg
  rw [mem_cenMod]
  intro w hw
  have hY : ∀ y ∈ fixV ρ.range, ρ g y = y := fun y hy => hy _ ⟨g, rfl⟩
  have hc := hg w hw
  have h3 : (ρ g w * w⁻¹) ^ 2 = 1 := h.hV _
  calc ρ (g ^ 2) w = ρ g (ρ g w) := by rw [pow_two, map_mul]; rfl
    _ = ρ g ((ρ g w * w⁻¹) * w) := by rw [inv_mul_cancel_right]
    _ = ρ g (ρ g w * w⁻¹) * ρ g w := map_mul _ _ _
    _ = (ρ g w * w⁻¹) * ((ρ g w * w⁻¹) * w) := by rw [hY _ hc, inv_mul_cancel_right]
    _ = (ρ g w * w⁻¹) ^ 2 * w := by rw [pow_two]; comm_group
    _ = w := by rw [h3, one_mul]

theorem pCoreOf_le_cenW [Finite Γ] : pCoreOf 2 (⊤ : Subgroup Γ) ≤ cenMod ρ (wMod ρ T) := by
  have hS : IsSylowIn 2 T ⊤ := h.minpar.syl
  have hle : pCoreOf 2 (⊤ : Subgroup Γ) ≤ T :=
    hS.le_of_normal le_top
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2 (le_normalizer_pCoreOf 2 ⊤))
      (pCoreOf_isPGroup 2 ⊤)
  intro r hr
  rw [mem_cenMod]
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨g, z, hz, rfl⟩ := hw
    have h1 : g⁻¹ * r * g ∈ pCoreOf 2 (⊤ : Subgroup Γ) := by
      have := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf 2 (⊤ : Subgroup Γ) (Subgroup.mem_top g⁻¹)) r).1 hr
      simpa using this
    have h2 : ρ (g⁻¹ * r * g) z = z := mem_fixV.1 hz _ (Subgroup.mem_map_of_mem ρ (hle h1))
    calc ρ r (ρ g z) = ρ (r * g) z := by rw [map_mul]; rfl
      _ = ρ (g * (g⁻¹ * r * g)) z := by rw [show g * (g⁻¹ * r * g) = r * g by group]
      _ = ρ g (ρ (g⁻¹ * r * g) z) := by rw [map_mul]; rfl
      _ = ρ g z := by rw [h2]
  | one => simp
  | mul y z _ _ ihy ihz =>
    rw [map_mul, ihy, ihz]
  | inv y _ ih =>
    rw [map_inv, ih]

theorem not_top_le_sup : ¬ (⊤ : Subgroup Γ) ≤ T ⊔ cenMod ρ (wMod ρ T) := by
  intro htop
  have hT : T ≤ cenMod ρ (fixV (T.map ρ)) := fun t ht z hz =>
    mem_fixV.1 hz _ (Subgroup.mem_map_of_mem ρ ht)
  have hD : cenMod ρ (wMod ρ T) ≤ cenMod ρ (fixV (T.map ρ)) := fun g hg z hz =>
    mem_cenMod.1 hg z (fixV_le_wMod ρ T hz)
  obtain ⟨g, z, hz, hgz⟩ := h.nontriv
  exact hgz (mem_cenMod.1 ((htop.trans (sup_le hT hD)) (Subgroup.mem_top g)) z hz)

variable [Finite V] [Finite Γ]

omit [Finite V] in
theorem ker_secF_le : (secF ρ T).ker ⊓ ⊤ ≤ cenMod ρ (wMod ρ T) ∧ (secF ρ T).ker ⊓ ⊤ ≤ M :=
  ker_inf_le_of_minPar (secF ρ T) h.minpar normalizer_cenW
    (fun g _ hg => ⟨1, by rw [pow_one]; exact h.sq_mem_cenW hg⟩) h.not_top_le_sup
    h.pCoreOf_le_cenW

theorem pCoreOf_map_secF : pCoreOf 2 ((⊤ : Subgroup Γ).map (secF ρ T)) = ⊥ :=
  pCoreOf_map_eq_bot (secF ρ T) h.minpar le_top normalizer_cenW cenW_le_ker
    h.ker_secF_le.1 h.not_top_le_sup h.pCoreOf_le_cenW

omit [Finite V] in
theorem map_maximal_secF :
    M.map (secF ρ T) < (⊤ : Subgroup Γ).map (secF ρ T) ∧
      ∀ Y : Subgroup (MulAut (Sec (wMod ρ T) (fixV ρ.range))),
        M.map (secF ρ T) ≤ Y → Y ≤ (⊤ : Subgroup Γ).map (secF ρ T) →
        Y = M.map (secF ρ T) ∨ Y = (⊤ : Subgroup Γ).map (secF ρ T) :=
  map_maximal (secF ρ T) h.minpar.lt_P (fun _ hMX hXP => h.minpar.maximal hMX hXP)
    h.ker_secF_le.2

theorem isSylowOf_map_secF : IsSylowOf 2 (T.map (secF ρ T)) (M.map (secF ρ T)) :=
  isSylowOf_map (secF ρ T)
    (isSylowOf_of_le_of_le h.minpar.syl h.minpar.le_M le_top)

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
