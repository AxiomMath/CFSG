module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatFrame
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatSq
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3ULemma
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open CFSG.Fischer
open CFSG.LargeExtraspecial (pointRadical)
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open CFSG.LargeExtraspecial.OrthoF2 (zmod2_eq_zero_or_eq_one)
open CFSG.ClassicalGroups.Orthogonal (eichler)
open Sec3SHatSq (indic indic_eq_zero_iff indic_mul)

namespace Sec3Theta

@[expose] def toF4 : ZMod 2 →+* F4 := ZMod.castHom (dvd_refl 2) F4

theorem toF4_injective : Function.Injective toF4 := toF4.injective

theorem toF4_code_lt (c : ZMod 2) : (toF4 c).code.val < 2 := by
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [map_zero]
    decide
  · rw [map_one]
    decide

@[expose] def epsF (y : Fin 6 → ZMod 2) : Census.V₀ := fun i => toF4 (y i)

theorem epsF_add (y y' : Fin 6 → ZMod 2) : epsF (y + y') = epsF y + epsF y' := by
  funext i
  simp [epsF]

theorem epsF_injective : Function.Injective epsF := fun _ _ h =>
  funext fun i => toF4_injective (congrFun h i)

theorem epsF_mem_N0 (y : Fin 6 → ZMod 2) : epsF y ∈ Census.N0 := fun i => toF4_code_lt (y i)

theorem exists_epsF {v : Census.V₀} (hv : v ∈ Census.N0) : ∃ y, epsF y = v := by
  refine ⟨fun i => ((v i).code.val : ZMod 2), funext fun i => Census.F4_eq_of_val ?_⟩
  have h := hv i
  rcases (show (v i).code.val = 0 ∨ (v i).code.val = 1 by omega) with h0 | h1
  · simp only [epsF, h0, Nat.cast_zero, map_zero]
    rfl
  · simp only [epsF, h1, Nat.cast_one, map_one]
    rfl

theorem Q₀_epsF (y : Fin 6 → ZMod 2) : Census.Q₀ (epsF y) = toF4 (Sec3Coord.qplus y) := by
  rw [Census.Q₀_apply]
  simp only [Census.qF, epsF, Sec3Coord.qplus, map_add, map_mul, pow_two]

theorem zmod2_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
  · rfl
  · exact absurd (h.mp rfl) (by decide)
  · exact absurd (h.mpr rfl) (by decide)
  · rfl

variable {G : Type} [Group G]

@[expose] noncomputable def iota (z e c : G) : F4 :=
  toF4 (indic (zpowers e) c) + F4.ω * toF4 (indic (zpowers z) c)

@[expose] noncomputable def theta (z e : G) (t : Fin 6 → G) (s : G) : Census.V₀ :=
  fun i => iota z e (s * t (Sec3Coord.piF i) * s⁻¹ * (t (Sec3Coord.piF i))⁻¹)

theorem indic_of_mem {K : Subgroup G} {c : G} (h : c ∈ K) : indic K c = 0 :=
  indic_eq_zero_iff.mpr h

theorem indic_of_not_mem {K : Subgroup G} {c : G} (h : c ∉ K) : indic K c = 1 :=
  CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero fun h' => h (indic_eq_zero_iff.mp h')

theorem iota_one (z e : G) : iota z e (1 : G) = 0 := by
  rw [iota, indic_of_mem (one_mem _), indic_of_mem (one_mem _), map_zero, mul_zero, add_zero]

theorem iota_inv (z e : G) {c : G} (hc : c * c = 1) : iota z e c⁻¹ = iota z e c := by
  rw [inv_eq_of_mul_eq_one_right hc]

theorem theta_apply (z e : G) (t : Fin 6 → G) (s : G) (i : Fin 6) :
    theta z e t s i = iota z e (s * t (Sec3Coord.piF i) * s⁻¹ * (t (Sec3Coord.piF i))⁻¹) := rfl

end Sec3Theta

open Sec3Theta

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)

structure ThetaHyp (e : G) (b : Fin 6 → H.xsub.Qt) (t : Fin 6 → G) : Prop where
  hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range
  hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)
  hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
    centralizer (sec3F (Q₀ ⊔ Q) : Set G)
  hZQ : Zs ≤ Q
  he : e ∈ Zs
  hez : e ∉ zpowers z
  pair : ∃ s₁ ∈ sec3SHat (Q₀ ⊔ Q) Zs, ∃ s₂ ∈ sec3SHat (Q₀ ⊔ Q) Zs,
    (∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₁ * u * s₁⁻¹ * u⁻¹ ∈ zpowers e) ∧
    (∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s₂ * u * s₂⁻¹ * u⁻¹ ∈ zpowers e) ∧
    s₁ * s₂ * s₁⁻¹ * s₂⁻¹ = z * e
  frame : Sec3Coord.IsFrame H.xsub.q b
  frame_perp : ∀ i, polar H.xsub.q (H.xsub.cl e) (b i) = 0
  frame_q : ∀ v, polar H.xsub.q (H.xsub.cl e) v = 0 →
    H.xsub.q v = Sec3Coord.qplus (Sec3Coord.coord H.xsub.q b v)
  frame_W₀ : b 0 ∈ H.xsub.clSub Q₀ ∧ b 1 ∈ H.xsub.clSub Q₀
  frame_x : H.ρG ⟨x, H.x_mem_N⟩ (b 0) = b 1 ∧ H.ρG ⟨x, H.x_mem_N⟩ (b 1) = b 0 + b 1
  frame_W' : ∀ i : Fin 6, 2 ≤ i.val → b i ∈ H.xsub.clSub Q
  lift_mem : ∀ j, t j ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)
  lift_cl : ∀ j, H.xsub.cl (t j) = b j

include H in
theorem exists_thetaHyp
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) : ∃ e b t, H.ThetaHyp e b t := by
  obtain ⟨e, he, hez, s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := H.exists_SHat_comm hΩ hQF hRc hZQ
  obtain ⟨b, hb, hperp, hq, hW₀, hW₀', hx0, hx1, hW'⟩ := H.exists_frame hZQ he hez
  have hU := H.centralizer_Zs_eq_clPre hZQ he hez
  have ht : ∀ j, ∃ t ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), H.xsub.cl t = b j := by
    intro j
    obtain ⟨t, htQ, htb⟩ := H.xsub.exists_cl (b j)
    refine ⟨t, ?_, htb⟩
    rw [hU]
    refine ⟨htQ, mem_perp.mpr fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [polar_smul_left, htb, hperp j, smul_zero]
  choose t ht htb using ht
  exact ⟨e, b, t, hΩ, hQF, hRc, hZQ, he, hez, ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩, hb, hperp, hq,
    ⟨hW₀, hW₀'⟩, ⟨hx0, hx1⟩, hW', ht, htb⟩

namespace ThetaHyp

variable {H} {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem mem_cases {c : G} (hc : c ∈ Zs) : c = 1 ∨ c = z ∨ c = e ∨ c = e * z :=
  H.mem_Zs_cases hT.hZQ hT.he hT.hez hc

theorem z_not_mem : z ∉ zpowers e := H.sq_z_not_mem_zpowers hT.he hT.hez

theorem iota_mul {c d : G} (hc : c ∈ Zs) (hd : d ∈ Zs) :
    iota z e (c * d) = iota z e c + iota z e d := by
  simp only [iota]
  rw [indic_mul (H.sq_mul_mem_zpowers_e hT.hZQ hT.he hT.hez) hc hd,
    indic_mul (H.sq_mul_mem_zpowers_z hT.hZQ hT.he hT.hez) hc hd, map_add, map_add]
  ring

theorem iota_z : iota z e z = 1 := by
  rw [iota, indic_of_not_mem hT.z_not_mem, indic_of_mem (mem_zpowers z), map_one, map_zero,
    mul_zero, add_zero]

theorem iota_e : iota z e e = F4.ω := by
  rw [iota, indic_of_mem (mem_zpowers e), indic_of_not_mem hT.hez, map_one, map_zero, mul_one,
    zero_add]

theorem iota_eq_zero_iff {c : G} (hc : c ∈ Zs) : iota z e c = 0 ↔ c = 1 := by
  constructor
  · intro h
    rcases hT.mem_cases hc with rfl | rfl | rfl | rfl
    · rfl
    · rw [hT.iota_z] at h
      exact absurd h (by decide)
    · rw [hT.iota_e] at h
      exact absurd h (by decide)
    · rw [H.comm_of_mem_Zs hT.he H.z_mem_Zs, hT.iota_mul H.z_mem_Zs hT.he, hT.iota_z,
        hT.iota_e] at h
      exact absurd h (by decide)
  · rintro rfl
    exact iota_one z e

omit [Finite G] hT in
theorem iota_of_mem_zpowers_z {c : G} (hc : c ∈ zpowers z) :
    iota z e c = toF4 (indic (zpowers e) c) := by
  have h : indic (zpowers z) c = 0 := indic_eq_zero_iff.mpr hc
  simp [iota, h]

omit [Finite G] hT in
theorem iota_of_mem_zpowers_e {c : G} (hc : c ∈ zpowers e) :
    iota z e c = F4.ω * toF4 (indic (zpowers z) c) := by
  have h : indic (zpowers e) c = 0 := indic_eq_zero_iff.mpr hc
  simp [iota, h]

theorem eq_one_of_mem {c : G} (hz : c ∈ zpowers z) (he : c ∈ zpowers e) : c = 1 := by
  rcases Sec3SHat.eq_one_or_eq_of_mem_zpowers (H.sq_mul_self_of_mem_Zs hT.he) he with h | h
  · exact h
  · exact absurd (h ▸ hz) hT.hez


theorem iota_ze : iota z e (z * e) = F4.ω + 1 := by
  rw [hT.iota_mul H.z_mem_Zs hT.he, hT.iota_z, hT.iota_e, add_comm]

omit [Finite G] hT in
theorem SHat_le_C : sec3SHat (Q₀ ⊔ Q) Zs ≤ centralizer (Zs : Set G) :=
  Sec3SHatSq.SHat_le_centralizer Q₀ Q Zs

theorem comm_mem {s u : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) : s * u * s⁻¹ * u⁻¹ ∈ Zs :=
  H.commutator_mem_Zs_of_mem_U hT.hΩ hT.hQF hT.hZQ hT.he hT.hez hs hu

theorem comm_mem_SHat {s s' : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs' : s' ∈ sec3SHat (Q₀ ⊔ Q) Zs) : s * s' * s⁻¹ * s'⁻¹ ∈ Zs := by
  have h := Subgroup.commutator_mem_commutator hs hs'
  rw [commutatorElement_def] at h
  exact H.commutator_SHat_le hT.hΩ hT.hQF hT.hZQ hT.he hT.hez h

theorem mul_self_mem {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) : s * s ∈ Zs :=
  H.mul_self_mem_Zs hT.hΩ hT.hQF hT.hZQ hT.he hT.hez hs

theorem theta_mul {s s' : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs' : s' ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    theta z e t (s * s') = theta z e t s + theta z e t s' := by
  funext i
  simp only [theta_apply, Pi.add_apply]
  have hc' := hT.comm_mem hs' (hT.lift_mem (Sec3Coord.piF i))
  have hcomm : Commute s (s' * t (Sec3Coord.piF i) * s'⁻¹ * (t (Sec3Coord.piF i))⁻¹) :=
    (mem_centralizer_iff.mp (SHat_le_C hs) _ hc').symm
  rw [Sec3SHatSq.comm_mul_left hcomm,
    hT.iota_mul hc' (hT.comm_mem hs (hT.lift_mem (Sec3Coord.piF i))), add_comm]

theorem theta_U {u : G} (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    theta z e t u = epsF (Sec3Coord.coord H.xsub.q b (H.xsub.cl u)) := by
  funext i
  simp only [theta_apply, epsF, Sec3Coord.coord_apply]
  have hr := hT.lift_mem (Sec3Coord.piF i)
  have hcz : u * t (Sec3Coord.piF i) * u⁻¹ * (t (Sec3Coord.piF i))⁻¹ ∈ zpowers z :=
    H.commutator_mem_zpowers hu.1 hr.1
  rw [iota_of_mem_zpowers_z hcz, ← hT.lift_cl (Sec3Coord.piF i)]
  congr 1
  apply zmod2_eq_of_iff
  rw [indic_eq_zero_iff, H.xsub.polar_cl_eq_zero_iff hu.1 hr.1, ← comm_eq_one_iff]
  exact ⟨fun h => hT.eq_one_of_mem hcz h, fun h => h ▸ one_mem _⟩

theorem iota_comm_typeA {s : G} (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e)
    {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hρ : H.ρF ⟨s, hsF⟩ = eichler H.xsub.q (H.xsub.cl e) w) {u : G}
    (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    iota z e (s * u * s⁻¹ * u⁻¹) = F4.ω * toF4 (polar H.xsub.q (H.xsub.cl u) w) := by
  have hce := hsU u hu
  rw [iota_of_mem_zpowers_e hce]
  congr 2
  apply zmod2_eq_of_iff
  have huQ : u ∈ H.xsub.Q₁ := hu.1
  have hsN := H.F_le_N hsF
  have hsu : s * u * s⁻¹ ∈ H.xsub.Q₁ := H.xsub.conj_mem hsN huQ
  have hcQ : s * u * s⁻¹ * u⁻¹ ∈ H.xsub.Q₁ := mul_mem hsu (inv_mem huQ)
  have hua : polar H.xsub.q (H.xsub.cl u) (H.xsub.cl e) = 0 :=
    (H.xsub.polar_cl_eq_zero_iff huQ (H.Q_le (hT.hZQ hT.he))).mpr
      (mem_centralizer_iff.mp hu.2 e hT.he).symm
  have hcl : H.xsub.cl (s * u * s⁻¹ * u⁻¹) =
      polar H.xsub.q (H.xsub.cl u) w • H.xsub.cl e := by
    rw [H.xsub.cl_mul hsu (inv_mem huQ), H.xsub.cl_inv huQ,
      (show H.ρF ⟨s, hsF⟩ (H.xsub.cl u) = H.xsub.cl (s * u * s⁻¹) from H.ρG_cl _ huQ).symm, hρ,
      CFSG.ClassicalGroups.Orthogonal.eichler_apply (H.q_cl_eq_zero hT.hZQ hT.he) hw, hua,
      zero_smul, add_zero, mul_zero, add_zero, sub_eq_add_neg, ZModModule.neg_eq_self,
      add_comm (H.xsub.cl u), add_assoc, ZModModule.add_self, add_zero]
  rw [indic_eq_zero_iff]
  change _ ∈ zpowers H.xsub.z ↔ _
  rw [← H.xsub.cl_eq_zero_iff hcQ, hcl, smul_eq_zero]
  exact ⟨fun h => h.resolve_right (H.cl_ne_zero hT.hZQ hT.he hT.hez), Or.inl⟩

theorem theta_typeA {s : G} (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e)
    {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hρ : H.ρF ⟨s, hsF⟩ = eichler H.xsub.q (H.xsub.cl e) w) :
    theta z e t s = F4.ω • epsF (Sec3Coord.coord H.xsub.q b w) := by
  funext i
  simp only [theta_apply, Pi.smul_apply, smul_eq_mul, epsF, Sec3Coord.coord_apply]
  rw [hT.iota_comm_typeA hsF hsU hw hρ (hT.lift_mem _), hT.lift_cl, polar_comm]


theorem iota_mul_self_U {u : G} (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    iota z e (u * u) = toF4 (H.xsub.q (H.xsub.cl u)) := by
  have huQ : u ∈ H.xsub.Q₁ := hu.1
  have hz : u * u ∈ zpowers z := by
    change u * u ∈ zpowers H.xsub.z
    rw [← H.xsub.cl_eq_zero_iff (mul_mem huQ huQ), H.xsub.cl_mul huQ huQ, ZModModule.add_self]
  rw [iota_of_mem_zpowers_z hz]
  congr 1
  apply zmod2_eq_of_iff
  rw [indic_eq_zero_iff, H.xsub.q_cl_eq_zero_iff huQ, pow_two]
  exact ⟨fun h => hT.eq_one_of_mem hz h, fun h => h ▸ one_mem _⟩

theorem iota_mul_self_typeA {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hsF : s ∈ sec3F (Q₀ ⊔ Q))
    (hsU : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), s * u * s⁻¹ * u⁻¹ ∈ zpowers e)
    {w : H.xsub.Qt} (hw : polar H.xsub.q (H.xsub.cl e) w = 0)
    (hρ : H.ρF ⟨s, hsF⟩ = eichler H.xsub.q (H.xsub.cl e) w) :
    iota z e (s * s) = (F4.ω + 1) * toF4 (H.xsub.q w) := by
  obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := hT.pair
  rw [H.mul_self_eq_of_comm_le hT.hΩ hT.hQF hT.hRc hT.hZQ hT.he hT.hez hs₁ hs₂ h1 h2 h12 hs hsF
    hsU hw hρ]
  rcases zmod2_eq_zero_or_eq_one (H.xsub.q w) with h | h
  · rw [h]
    simp [iota_one]
  · rw [h]
    simp [hT.iota_ze]

theorem Q₀_theta {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    Census.Q₀ (theta z e t s) = iota z e (s * s) := by
  have hsF : s ∈ sec3F (Q₀ ⊔ Q) := Sec3SHatSq.SHat_le_F Q₀ Q Zs hs
  have ha0 := H.cl_ne_zero hT.hZQ hT.he hT.hez
  have hqa := H.q_cl_eq_zero hT.hZQ hT.he
  have hρs := H.ρF_mem_pointRadical hT.hΩ hT.hQF hT.hZQ hT.he hT.hez (s := ⟨s, hsF⟩) hs
  obtain ⟨se, hseS, hseρ, hseU⟩ :=
    H.exists_mem_SHatE hT.hΩ hT.hQF hT.hRc hT.hZQ hT.he hT.hez hρs
  obtain ⟨w, hw, hρw⟩ :=
    (CFSG.LargeExtraspecial.mem_pointRadical_iff H.xsub.q_nondegenerate ha0 hqa).mp hρs
  have hseE : H.ρF ⟨(se : G), se.2⟩ = eichler H.xsub.q (H.xsub.cl e) w := hseρ.trans hρw
  have huS : (se : G)⁻¹ * s ∈ sec3SHat (Q₀ ⊔ Q) Zs := mul_mem (inv_mem hseS) hs
  have huF : (se : G)⁻¹ * s ∈ sec3F (Q₀ ⊔ Q) := mul_mem (inv_mem se.2) hsF
  have huρ : H.ρF ⟨(se : G)⁻¹ * s, huF⟩ = 1 := by
    have e1 : (⟨(se : G)⁻¹ * s, huF⟩ : ↥(sec3F (Q₀ ⊔ Q))) = se⁻¹ * ⟨s, hsF⟩ := rfl
    rw [e1, map_mul, map_inv, hseρ, inv_mul_cancel]
  have huU := H.mem_U_of_mem_SHat hT.hQF hT.hZQ (s := ⟨(se : G)⁻¹ * s, huF⟩) huS huρ
  set u := (se : G)⁻¹ * s with hu
  have hsu : s = se * u := by rw [hu]; group
  have hcU : (se : G) * u * (se : G)⁻¹ * u⁻¹ ∈ Zs := hT.comm_mem hseS huU
  have hcU' : u * se * u⁻¹ * (se : G)⁻¹ ∈ Zs := by
    have e1 : u * se * u⁻¹ * (se : G)⁻¹ = ((se : G) * u * (se : G)⁻¹ * u⁻¹)⁻¹ := by group
    rw [e1]
    exact inv_mem hcU
  have hcomm : Commute (se : G) (u * se * u⁻¹ * (se : G)⁻¹) :=
    (mem_centralizer_iff.mp (SHat_le_C hseS) _ hcU').symm
  have hss : iota z e (s * s) = F4.ω * toF4 (polar H.xsub.q (H.xsub.cl u) w) +
      (F4.ω + 1) * toF4 (H.xsub.q w) + toF4 (H.xsub.q (H.xsub.cl u)) := by
    rw [hsu, Sec3SHatSq.mul_mul_self hcomm, hT.iota_mul (mul_mem hcU' (hT.mul_self_mem hseS))
      (hT.mul_self_mem huS), hT.iota_mul hcU' (hT.mul_self_mem hseS),
      hT.iota_mul_self_U huU, hT.iota_mul_self_typeA hseS se.2 hseU hw hseE]
    congr 2
    have e1 : u * se * u⁻¹ * (se : G)⁻¹ = ((se : G) * u * (se : G)⁻¹ * u⁻¹)⁻¹ := by group
    rw [e1, iota_inv z e (H.sq_mul_self_of_mem_Zs hcU), hT.iota_comm_typeA se.2 hseU hw hseE huU]
  have hθ : theta z e t s = F4.ω • epsF (Sec3Coord.coord H.xsub.q b w) +
      epsF (Sec3Coord.coord H.xsub.q b (H.xsub.cl u)) := by
    rw [hsu, hT.theta_mul hseS huS, hT.theta_typeA se.2 hseU hw hseE, hT.theta_U huU]
  have hua : polar H.xsub.q (H.xsub.cl e) (H.xsub.cl u) = 0 :=
    (H.xsub.polar_cl_eq_zero_iff (H.Q_le (hT.hZQ hT.he)) huU.1).mpr
      (mem_centralizer_iff.mp huU.2 e hT.he)
  have hwu : polar H.xsub.q (H.xsub.cl e) (w + H.xsub.cl u) = 0 := by
    rw [polar_add_right, hw, hua, add_zero]
  have hqw := hT.frame_q w hw
  have hqu := hT.frame_q _ hua
  have hqwu := hT.frame_q _ hwu
  have hpol : polar Census.Q₀ (epsF (Sec3Coord.coord H.xsub.q b w))
      (epsF (Sec3Coord.coord H.xsub.q b (H.xsub.cl u))) =
      toF4 (polar H.xsub.q w (H.xsub.cl u)) := by
    rw [polar, ← epsF_add, ← map_add, Q₀_epsF, Q₀_epsF, Q₀_epsF, ← hqw, ← hqu, ← hqwu, polar,
      map_sub, map_sub]
  rw [hss, hθ, map_add_eq, QuadraticMap.map_smul, polar_smul_left, hpol, Q₀_epsF, Q₀_epsF, ← hqw,
    ← hqu, smul_eq_mul, smul_eq_mul, polar_comm H.xsub.q w]
  have hω : F4.ω * F4.ω = F4.ω + 1 := by decide
  rw [hω]
  ring

theorem polar_theta {s s' : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs' : s' ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    polar Census.Q₀ (theta z e t s) (theta z e t s') = iota z e (s' * s * s'⁻¹ * s⁻¹) := by
  have hc := hT.comm_mem_SHat hs' hs
  have hcomm : Commute s (s' * s * s'⁻¹ * s⁻¹) :=
    (mem_centralizer_iff.mp (SHat_le_C hs) _ hc).symm
  rw [polar, ← hT.theta_mul hs hs', hT.Q₀_theta (mul_mem hs hs'), hT.Q₀_theta hs, hT.Q₀_theta hs',
    Sec3SHatSq.mul_mul_self hcomm, hT.iota_mul (mul_mem hc (hT.mul_self_mem hs))
    (hT.mul_self_mem hs'), hT.iota_mul hc (hT.mul_self_mem hs)]
  ring

theorem theta_eq_zero_iff {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    theta z e t s = 0 ↔ s ∈ Zs := by
  constructor
  · intro h
    rw [← H.centerIn_SHat hT.hΩ hT.hQF hT.hZQ hT.he hT.hez]
    refine ⟨hs, mem_centralizer_iff.mpr fun s' hs' => ?_⟩
    have h1 := hT.polar_theta hs' hs
    rw [h, polar_zero_right, eq_comm, hT.iota_eq_zero_iff (hT.comm_mem_SHat hs hs'),
      comm_eq_one_iff] at h1
    exact h1.symm
  · intro h
    funext i
    have hr := hT.lift_mem (Sec3Coord.piF i)
    rw [theta_apply, mem_centralizer_iff.mp hr.2 s h, mul_inv_cancel_right, mul_inv_cancel,
      iota_one]
    rfl

theorem theta_one : theta z e t 1 = 0 :=
  (hT.theta_eq_zero_iff (one_mem _)).mpr (one_mem _)

theorem theta_inv {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    theta z e t s⁻¹ = -theta z e t s := by
  have h := hT.theta_mul hs (inv_mem hs)
  rw [mul_inv_cancel, hT.theta_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem theta_eq_iff {s s' : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hs' : s' ∈ sec3SHat (Q₀ ⊔ Q) Zs) : theta z e t s = theta z e t s' ↔ s'⁻¹ * s ∈ Zs := by
  rw [← hT.theta_eq_zero_iff (mul_mem (inv_mem hs') hs), hT.theta_mul (inv_mem hs') hs,
    hT.theta_inv hs', neg_add_eq_zero, eq_comm]

theorem theta_surjective (v : Census.V₀) :
    ∃ s ∈ sec3SHat (Q₀ ⊔ Q) Zs, theta z e t s = v := by
  let φ : ↥(sec3SHat (Q₀ ⊔ Q) Zs) →* Multiplicative Census.V₀ :=
    { toFun := fun s => Multiplicative.ofAdd (theta z e t s)
      map_one' := by
        change Multiplicative.ofAdd (theta z e t 1) = 1
        rw [hT.theta_one, ofAdd_zero]
      map_mul' := fun s s' => by
        change Multiplicative.ofAdd (theta z e t (s * s')) = _
        rw [hT.theta_mul s.2 s'.2, ofAdd_add] }
  have hZS : Zs ≤ sec3SHat (Q₀ ⊔ Q) Zs := (H.Zs_le_U hT.hZQ).trans (H.U_le_SHat hT.hQF)
  have hker : φ.ker = Zs.subgroupOf (sec3SHat (Q₀ ⊔ Q) Zs) := by
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hT.theta_eq_zero_iff s.2]
    change Multiplicative.ofAdd (theta z e t s) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe hZS).toEquiv, H.q0.dData.suz.Zs_card,
    H.card_SHat hT.hΩ hT.hQF hT.hRc hT.hZQ hT.he hT.hez] at hcard
  have hV : Nat.card (Multiplicative Census.V₀) = 4096 := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_fun, Nat.card_eq_fintype_card,
      F4.card, Nat.card_fin]
    norm_num
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hV]; omega)
  obtain ⟨s, hs⟩ := MonoidHom.range_eq_top.mp htop (Multiplicative.ofAdd v)
  exact ⟨s, s.2, Multiplicative.ofAdd.injective hs⟩

theorem theta_image_U :
    theta z e t '' ((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) = Census.N0 := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hT.theta_U hu]
    exact epsF_mem_N0 _
  · intro hv
    obtain ⟨y, rfl⟩ := exists_epsF hv
    obtain ⟨u, huQ, hub⟩ := H.xsub.exists_cl (Sec3Coord.vec b y)
    have hya : polar H.xsub.q (H.xsub.cl e) (Sec3Coord.vec b y) = 0 := by
      rw [polar_comm]
      exact Sec3Coord.polar_vec_left (fun i => by rw [polar_comm]; exact hT.frame_perp i) y
    have huU : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
      rw [H.centralizer_Zs_eq_clPre hT.hZQ hT.he hT.hez]
      refine ⟨huQ, mem_perp.mpr fun w hw => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [polar_smul_left, hub, hya, smul_zero]
    exact ⟨u, huU, by rw [hT.theta_U huU, hub, Sec3Coord.coord_vec hT.frame]⟩

theorem mem_U_of_theta_mem {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hθ : theta z e t s ∈ Census.N0) : s ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
  rw [← hT.theta_image_U] at hθ
  obtain ⟨u, hu, huθ⟩ := hθ
  have h := (hT.theta_eq_iff hs (H.U_le_SHat hT.hQF hu)).mp huθ.symm
  rw [show s = u * (u⁻¹ * s) by group]
  exact mul_mem hu (H.Zs_le_U hT.hZQ h)

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81
