module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ODefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OSq
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ORho
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Hyp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aX
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem z4o_card_cent_eq [Finite G] {V B : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB16 : Nat.card B = 2 ^ 4) {φ : (Fin 5 → ZMod 2) → G} (hφ : SecNatCoord φ B) {h : G}
    {a b c d e : Fin 5} (hab : a ≠ b)
    (hspan : ∀ x : Fin 5 → ZMod 2, IsEvenVec x → x a = x b →
      x = 0 ∨ x = wvec c ∨ x = wvec d ∨ x = wvec e ∨ x = wvec c + wvec d ∨
        x = wvec c + wvec e ∨ x = wvec d + wvec e ∨ x = wvec c + wvec d + wvec e)
    (hact : SecActs φ h (Equiv.swap a b)) {vc vd ve : G}
    (hvc : vc ∈ V ⊓ centralizer ({h} : Set G)) (hvd : vd ∈ V ⊓ centralizer ({h} : Set G))
    (hve : ve ∈ V ⊓ centralizer ({h} : Set G)) (hc : vc * vc = φ (wvec c))
    (hd : vd * vd = φ (wvec d)) (he : ve * ve = φ (wvec e)) :
    Nat.card ↥(V ⊓ centralizer ({h} : Set G)) = 2 ^ 6 := by
  have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => hφ.mul_self_eq_one hx
  obtain ⟨D2, hD2B, hD2sq, hcard⟩ := z4o_exists_sq hV hBV hB16 hB2
    (inf_le_left : V ⊓ centralizer ({h} : Set G) ≤ V)
  have hDB : V ⊓ centralizer ({h} : Set G) ⊓ B = B ⊓ centralizer ({h} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hBV hx.1, hx.2⟩, hx.1⟩⟩
  have hD2eq : D2 = B ⊓ centralizer ({h} : Set G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, hvx⟩ := (hD2sq x).mp hx
      have hvC := (Subgroup.mem_inf.mp hv).2
      refine Subgroup.mem_inf.mpr ⟨hD2B hx, ?_⟩
      rw [← hvx]
      exact (centralizer ({h} : Set G)).mul_mem hvC hvC
    · intro x hx
      obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨u, hu, rfl⟩ := hφ.onto x hxB
      have hfix : permVec (Equiv.swap a b) u = u := by
        refine hφ.inj _ _ (isEvenVec_permVec _ hu) hu ?_
        rw [← hact u hu]
        have hcomm : h * φ u = φ u * h :=
          Subgroup.mem_centralizer_iff.mp hxC h (Set.mem_singleton h)
        rw [hcomm, mul_inv_cancel_right]
      have hab' : u a = u b := by
        have h1 := congrFun hfix a
        simp only [permVec, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h1
        exact h1.symm
      have hwc : φ (wvec c) ∈ D2 := (hD2sq _).mpr ⟨vc, hvc, hc⟩
      have hwd : φ (wvec d) ∈ D2 := (hD2sq _).mpr ⟨vd, hvd, hd⟩
      have hwe : φ (wvec e) ∈ D2 := (hD2sq _).mpr ⟨ve, hve, he⟩
      have hmul : ∀ i j : Fin 5, φ (wvec i) ∈ D2 → φ (wvec j) ∈ D2 →
          φ (wvec i + wvec j) ∈ D2 := fun i j hi hj => by
        rw [hφ.mul _ _ (wvec_even i) (wvec_even j)]
        exact D2.mul_mem hi hj
      rcases hspan u hu hab' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hφ.map_zero]
        exact D2.one_mem
      · exact hwc
      · exact hwd
      · exact hwe
      · exact hmul c d hwc hwd
      · exact hmul c e hwc hwe
      · exact hmul d e hwd hwe
      · rw [hφ.mul _ _ (wvec_add_even c d) (wvec_even e)]
        exact D2.mul_mem (hmul c d hwc hwd) hwe
  rw [hcard, hDB, hD2eq, sec123_card_cent hφ hab hact]
  norm_num

theorem z4o_transport [Finite G] {t : G} {L S V : Subgroup G} (F : Sec12Frame t L S)
    (hBV : secB S L ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L))
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    (hYV : secM t S L ⊓ L ≤ normalizer (V : Set G)) {s : G}
    (hsY : s ∈ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G))
    (hsV : s ∈ normalizer (V : Set G)) {a b c d : Fin 5} (hs : SecActs φ s (Equiv.swap a b))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d)
    {vc : G} (hvc : vc ∈ V) (hvcc : vc * vc = φ (wvec c)) :
    ∃ vd ∈ V, vd * vd = φ (wvec d) ∧ (s * vc * s⁻¹ = vc → s * vd * s⁻¹ = vd) ∧
      (s * vc * s⁻¹ = vc⁻¹ → s * vd * s⁻¹ = vd⁻¹) := by
  have hπ : Equiv.swap c d * Equiv.swap a b ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hcd,
      Equiv.Perm.sign_swap hab]
    decide
  obtain ⟨y, hyY, hy⟩ := hperm.2.2.2.2 _ hπ
  have hy : SecActs φ y (Equiv.swap c d * Equiv.swap a b) := hy
  refine ⟨y * vc * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hYV hyY) vc).mp hvc, ?_, ?_⟩
  · calc y * vc * y⁻¹ * (y * vc * y⁻¹) = y * (vc * vc) * y⁻¹ := by group
      _ = φ (wvec d) := by
        rw [hvcc, hy _ (wvec_even c), permVec_wvec, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
  have hsyY : s * y * s⁻¹ ∈ secM t S L ⊓ L := (Subgroup.mem_normalizer_iff.mp hsY y).mp hyY
  have hsy : SecActs φ (s * y * s⁻¹) (Equiv.swap c d * Equiv.swap a b) := by
    have h := (hs.mul hy).mul (z4o_secActs_inv hs)
    rwa [z4o_swap_conj hca hcb hda hdb] at h
  have hkey : ∀ w ∈ V, s * (y * w * y⁻¹) * s⁻¹ = y * (s * w * s⁻¹) * y⁻¹ := by
    intro w hw
    have hsw : s * w * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsV w).mp hw
    have h := z4o_act_eq F hBV hVc hφ hsyY.2 hyY.2 hsy hy hsw
    calc s * (y * w * y⁻¹) * s⁻¹ = s * y * s⁻¹ * (s * w * s⁻¹) * (s * y * s⁻¹)⁻¹ := by group
      _ = y * (s * w * s⁻¹) * y⁻¹ := h
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hkey vc hvc, h]
  · rw [hkey vc hvc, h]
    group

theorem asc82StepZ4Cent_of (hp : Asc82Pre11) : Asc82StepZ4Cent := by
  intro G _ _ t L S z K1 K2 E hctx hZ s hs2 hsS hsK
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  obtain ⟨φ, hperm0, -, -, hS5⟩ := F.bdata.2.2.2.2.2
  have hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hperm0
  have hφ : SecNatCoord φ (secB S L) :=
    ⟨fun v hv => (hperm.2.2.1 _).mpr ⟨v, hv, rfl⟩, hperm.1, hperm.2.1,
      fun x hx => (hperm.2.2.1 x).mp hx⟩
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hVc := sec124_z4_comm hZ
  have hYV := sec121_Y_le_normalizer_V F hE
  have hsYc : s ∈ (secM t S L ⊓ L) ⊔ S := Subgroup.mem_sup_right hsS
  have hsY : s ∈ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) :=
    sec122_Yc_le_normalizer_Y F hS.1 hsYc
  have hsV : s ∈ normalizer (secV t S L E : Set G) :=
    sec122_Yc_le_normalizer_V F hS.1 hctx.S_norm hctx.ML_norm hsYc
  have hsNN := (sec123_Y_le F hS hsYc).1
  obtain ⟨τ, hτ⟩ := hS5 s hsNN
  have hτ : SecActs φ s τ := hτ
  have hss : s * s = 1 := by
    rw [← sq, ← hs2]
    exact pow_orderOf_eq_one s
  have hτ2 : τ * τ = 1 :=
    SecActs.unique hφ (hτ.mul hτ) (by rw [hss]; exact z4o_secActs_one φ)
  have hτodd : Equiv.Perm.sign τ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
    · exact absurd (z4o_mem_K_of_even F hperm hsNN.1 hτ
        (Equiv.Perm.mem_alternatingGroup.mpr h)) hsK
    · exact h
  obtain ⟨a, b, hab, rfl⟩ := sec123_swap_of_involution hτ2 hτodd
  obtain ⟨c, d, e, hca, hcb, hda, hdb, hea, heb, hcd, hce, -, hspan⟩ := z4o_three a b hab
  obtain ⟨vc, hvc, hvcc, hfc⟩ := z4o_exists_fix F hE hZ hperm c
  have hsinv : ∀ y ∈ secM t S L ⊓ L, s⁻¹ * y * s ∈ secM t S L ⊓ L := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hsY) y).mp hy
    rwa [inv_inv] at h
  have hfc' := z4o_fix_conj hsinv hτ (Equiv.swap_apply_of_ne_of_ne hca hcb) hfc
  have hsvc : s * vc * s⁻¹ ∈ secV t S L E := (Subgroup.mem_normalizer_iff.mp hsV vc).mp hvc
  have hsvcc : s * vc * s⁻¹ * (s * vc * s⁻¹) = φ (wvec c) := by
    calc s * vc * s⁻¹ * (s * vc * s⁻¹) = s * (vc * vc) * s⁻¹ := by group
      _ = φ (wvec c) := by
        rw [hvcc, hτ _ (wvec_even c), permVec_wvec, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hcase := z4o_fix_unique F hE hZ hperm hvc hsvc hvcc hsvcc hfc hfc'
  obtain ⟨vd, hvd, hvdd, hsd⟩ :=
    z4o_transport F hBV hVc hφ hperm hYV hsY hsV hτ hab hca hcb hda hdb hcd hvc hvcc
  obtain ⟨ve, hve, hvee, hse⟩ :=
    z4o_transport F hBV hVc hφ hperm hYV hsY hsV hτ hab hca hcb hea heb hce hvc hvcc
  rcases hcase with h | h
  · left
    have hmem : ∀ w ∈ secV t S L E, s * w * s⁻¹ = w →
        w ∈ secV t S L E ⊓ centralizer ({s} : Set G) := by
      intro w hw hsw
      refine Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      calc s * w = s * w * s⁻¹ * s := by group
        _ = w * s := by rw [hsw]
    exact z4o_card_cent_eq hZ hBV F.bdata.2.1 hφ hab hspan hτ (hmem _ hvc h)
      (hmem _ hvd (hsd.1 h)) (hmem _ hve (hse.1 h)) hvcc hvdd hvee
  · right
    have htinv := sec124_t_inv F hE hZ
    have htact : SecActs φ t 1 := by
      intro v hv
      rw [permVec_one]
      have hc : φ v * t = t * φ v :=
        Subgroup.mem_centralizer_iff.mp F.htC _ (F.bdata.1 (hφ.mem v hv))
      calc t * φ v * t⁻¹ = φ v * t * t⁻¹ := by rw [hc]
        _ = φ v := by group
    have hst : SecActs φ (s * t) (Equiv.swap a b) := by
      have h := hτ.mul htact
      rwa [mul_one] at h
    have hmem : ∀ w ∈ secV t S L E, s * w * s⁻¹ = w⁻¹ →
        w ∈ secV t S L E ⊓ centralizer ({s * t} : Set G) := by
      intro w hw hsw
      refine Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      have h1 : s * t * w * (s * t)⁻¹ = w := by
        calc s * t * w * (s * t)⁻¹ = s * (t * w * t⁻¹) * s⁻¹ := by group
          _ = s * w⁻¹ * s⁻¹ := by rw [htinv w hw]
          _ = (s * w * s⁻¹)⁻¹ := by group
          _ = w := by rw [hsw, inv_inv]
      calc s * t * w = s * t * w * (s * t)⁻¹ * (s * t) := by group
        _ = w * (s * t) := by rw [h1]
    exact z4o_card_cent_eq hZ hBV F.bdata.2.1 hφ hab hspan hst (hmem _ hvc h)
      (hmem _ hvd (hsd.2 h)) (hmem _ hve (hse.2 h)) hvcc hvdd hvee

end CFSG.OddStandard.SmallF3.Omega
