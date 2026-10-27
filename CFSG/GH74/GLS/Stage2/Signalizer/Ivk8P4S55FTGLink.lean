module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FrameParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGQuot
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55R3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace FTG

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {G : Type} [Group G] [Finite G]

structure CompData (H P : Subgroup G) (g : G) {Γ : Type} [Group Γ] (K : Subgroup Γ) [K.Normal]
    (P' : Subgroup Γ) (J : Subgroup (HBar H)) : Prop where
  comp : IsComponent J
  ncent : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H))
  quot : Nonempty ((↥K ⧸ center ↥K) ≃* (↥J ⧸ center ↥J))
  even : Even (Nat.card (center ↥K)) → Even (Nat.card (center ↥J))
  inner : J.Normal → ∀ x ∈ P', ∀ y : ↥K ⧸ center ↥K, y ≠ 1 → actY x = MulAut.conj y →
    ∃ h : ↥H, (h : G) ∈ P ∧ ∃ j ∈ J,
      j⁻¹ * QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ centralizer (J : Set (HBar H)) ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∉ centralizer (J : Set (HBar H))

theorem compData_of_link {k : Kind} {p : ℕ} {H P T : Subgroup G} {g : G} {Γ : Type} [Group Γ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
    {K : Subgroup Γ} [K.Normal] {a : Γ} {P' R : Subgroup Γ} (hf : Frame55 k p ρ K a P' R)
    (hl : Link55 H P T g K a P' R) : ∃ J : Subgroup (HBar H), CompData H P g K P' J := by
  obtain ⟨Γ₀, _, π, ι, hg, J, hι, -, -, -, -, hPm, -, hJ, hJc, Dl, hDlH, -, hDlJ, hDlK,
    hDlN⟩ := hl
  set q : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hq
  let incl : ↥Dl →* ↥H := Subgroup.inclusion hDlH
  have hincl : ∀ d : ↥Dl, ((incl d : ↥H) : G) = d := fun _ => rfl
  have hφmem : ∀ d : ↥Dl, q (incl d) ∈ J := fun d => by
    rw [← hDlJ]
    exact ⟨incl d, (Subgroup.mem_subgroupOf).mpr d.2, rfl⟩
  let φ : ↥Dl →* ↥J := (q.comp incl).codRestrict J hφmem
  have hφv : ∀ d : ↥Dl, ((φ d : ↥J) : HBar H) = q (incl d) := fun _ => rfl
  have hφ : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    rw [← hDlJ] at hj
    obtain ⟨h, hh, rfl⟩ := hj
    refine ⟨⟨(h : G), (Subgroup.mem_subgroupOf).mp hh⟩, Subtype.ext ?_⟩
    rw [hφv]
    rfl
  have hψmem : ∀ d : ↥Dl, π (incl d) ∈ K.map ι := fun d => by
    rw [← hDlK]
    exact ⟨incl d, (Subgroup.mem_subgroupOf).mpr d.2, rfl⟩
  let eK : ↥K ≃* ↥(K.map ι) := K.equivMapOfInjective ι hι
  have heK : ∀ u : ↥K, ((eK u : ↥(K.map ι)) : Γ₀) = ι u := fun _ => rfl
  let ψ : ↥Dl →* ↥K := eK.symm.toMonoidHom.comp ((π.comp incl).codRestrict (K.map ι) hψmem)
  have hψv : ∀ d : ↥Dl, ι (ψ d : Γ) = π (incl d) := by
    intro d
    rw [← heK]
    show (((eK (eK.symm ⟨π (incl d), hψmem d⟩)) : ↥(K.map ι)) : Γ₀) = π (incl d)
    rw [MulEquiv.apply_symm_apply]
  have hψ : Function.Surjective ψ := by
    intro u
    have hu : ι u ∈ (Dl.subgroupOf H).map π := by rw [hDlK]; exact ⟨u, u.2, rfl⟩
    obtain ⟨h, hh, hhu⟩ := hu
    refine ⟨⟨(h : G), (Subgroup.mem_subgroupOf).mp hh⟩, ?_⟩
    apply Subtype.ext
    apply hι
    rw [hψv]
    exact hhu
  have hodd : Odd (Nat.card φ.ker) := by
    have hO : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hle : φ.ker.map incl ≤ pPrimeCore 2 ↥H := by
      rintro _ ⟨d, hd, rfl⟩
      have h1 : q (incl d) = 1 := by
        rw [← hφv]
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hd)
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hc : Nat.card ↥(φ.ker.map incl) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDlH)
    exact Odd.of_dvd_nat hO (hc ▸ Subgroup.card_dvd_of_le hle)
  have hJq : IsQuasisimple ↥J := hJ.1
  have hKq : IsQuasisimple ↥K := hf.quasi
  set e := centerQuotEquiv hφ hψ hJq hKq hodd with he
  refine ⟨J, hJ, hJc, ⟨e.symm⟩, fun hev => even_card_center hφ hψ hJq hKq hodd hev, ?_⟩
  intro hJn x hx y hy1 hxy
  have hxm : ι x ∈ (P.subgroupOf H).map π := by rw [← hPm]; exact ⟨x, hx, rfl⟩
  obtain ⟨h, hhP, hhx⟩ := hxm
  have hqN : q h ∈ normalizer (J : Set (HBar H)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hJn]
    trivial
  have hhN : (h : G) ∈ normalizer (Dl : Set G) := hDlN h hqN
  let α : ↥Dl → ↥Dl := fun d =>
    ⟨(h : G) * d * (h : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hhN d).mp d.2⟩
  have hαH : ∀ d : ↥Dl, incl (α d) = h * incl d * h⁻¹ := fun _ => Subtype.ext rfl
  let β : MulAut ↥J := MulAut.conjNormal (q h)
  let γ : MulAut ↥K := MulAut.conjNormal x
  have hαβ : ∀ d : ↥Dl, φ (α d) = β (φ d) := by
    intro d
    apply Subtype.ext
    rw [hφv, MulAut.conjNormal_apply, hφv, hαH, map_mul, map_mul, map_inv]
  have hαγ : ∀ d : ↥Dl, ψ (α d) = γ (ψ d) := by
    intro d
    apply Subtype.ext
    apply hι
    rw [hψv, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, hψv, ← hhx, hαH, map_mul,
      map_mul, map_inv]
  have hγ : autBar γ = MulAut.conj y := hxy
  have hβ := exists_conj_of_conj hφ hψ hJq hKq hodd hαβ hαγ hγ
  rw [← he] at hβ
  set w := e.symm y with hw
  obtain ⟨j0, hj0⟩ := QuotientGroup.mk_surjective w
  have : Group.IsPerfect ↥J := hJq.1
  have hyβ : YCfg.yAct J ⟨q h, hqN⟩ = autBar β := by
    ext v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [YCfg.yAct_apply_mk, autBar_mk]
    congr 1
  have hyj : YCfg.yAct J ⟨(j0 : HBar H), le_normalizer j0.2⟩ = MulAut.conj w := by
    rw [YCfg.yAct_of_mem, YCfg.innHom_apply, hj0]
  have hjN : (j0 : HBar H)⁻¹ * q h ∈ normalizer (J : Set (HBar H)) :=
    mul_mem (inv_mem (le_normalizer j0.2)) hqN
  refine ⟨h, (Subgroup.mem_subgroupOf).mp hhP, (j0 : HBar H), j0.2, ?_, ?_⟩
  · have h1 : YCfg.yAct J ⟨(j0 : HBar H)⁻¹ * q h, hjN⟩ = 1 := by
      have h2 : (⟨(j0 : HBar H)⁻¹ * q h, hjN⟩ : ↥(normalizer (J : Set (HBar H)))) =
          (⟨(j0 : HBar H), le_normalizer j0.2⟩ : ↥(normalizer (J : Set (HBar H))))⁻¹ *
            ⟨q h, hqN⟩ := rfl
      rw [h2, map_mul, map_inv, hyj, hyβ, hβ, inv_mul_cancel]
    exact (YCfg.yAct_eq_one_iff J ⟨_, hjN⟩).mp h1
  · intro hc
    have h1 : YCfg.yAct J ⟨q h, hqN⟩ = 1 := (YCfg.yAct_eq_one_iff J ⟨q h, hqN⟩).mpr hc
    rw [hyβ, hβ] at h1
    have hw1 : w = 1 := eq_one_of_conj_eq_one (center_quot_eq_bot hJq) h1
    apply hy1
    rw [← e.apply_symm_apply y, ← hw, hw1, map_one]

theorem kindFactorAll_of_even_center (hInv : InvSec) {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) (H : Subgroup G) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hev : Even (Nat.card (center ↥J))) : KindFactorAll k (↥J ⧸ center ↥J) := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  set u : HBar H := ((x : ↥J) : HBar H) with hu
  have hu2 : orderOf u = 2 := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  have hJC : J ≤ centralizer ({u} : Set (HBar H)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_center_iff.mp x.2 ⟨v, hv⟩
    exact congrArg Subtype.val h1
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hJ.1.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hsec : IsSection (↥J ⧸ center ↥J) ↥J :=
    ⟨⊤, (QuotientGroup.mk' (center ↥J)).comp (⊤ : Subgroup ↥J).subtype, fun v => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
      exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩⟩
  exact hbar_invsec hInv hctx H u hu2 _ hns (IsSection.of_le_le hJC hsec)

end FTG

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
