module

public import CFSG.ClassicalInvolution.Generic.Frame
import CFSG.ClassicalInvolution.Asc77.AscE187P1a
import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
import CFSG.ClassicalInvolution.Asc77.AscE189Comp
import CFSG.Quasithin.Background.F7TwoInvBridge
import CFSG.Quasithin.Background.F7TwoDefs

public section

namespace CFSG.ClassicalInvolution

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.Quasithin.F7Two
open scoped MatrixGroups commutatorElement

theorem commute_mul_self_of_commutator_mem_center {G : Type*} [Group G] {z u : G}
    (hz : z * z = 1) (hc : ⁅z, u⁆ ∈ Subgroup.center G) : Commute z (u * u) := by
  have hzu : Commute u ⁅z, u⁆ := Subgroup.mem_center_iff.mp hc u
  have hzc : Commute z ⁅z, u⁆ := Subgroup.mem_center_iff.mp hc z
  have h1 : ⁅z, u ^ 2⁆ = 1 := by
    calc ⁅z, u ^ 2⁆ = ⁅z, u⁆ ^ 2 := (hzu.commutatorElement_pow_right 2).symm
      _ = ⁅z ^ 2, u⁆ := hzc.commutatorElement_pow_left 2
      _ = 1 := by rw [pow_two, hz]; simp
  exact commutatorElement_eq_one_iff_commute.mp (by simpa [pow_two] using h1)

namespace Disconnected.AschTight

variable {U X : Type} [Group U] [Group X]

theorem commutator_map_eq_bot_of_mulEquiv_sl2 [Finite U] [Finite X] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {R R' : Subgroup U} {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (eR : ↥R ≃* SL(2, F)) (hRk : R ⊓ ψ.ker = ⊥) (hR'k : R' ⊓ ψ.ker = ⊥)
    {z z' : U} (hz : IsUniqueInvolution R z) (hz' : IsUniqueInvolution R' z')
    (hW : Subgroup.centralizer ({z} : Set U) ≤ Subgroup.normalizer (R : Set U))
    (hW' : Subgroup.centralizer ({z'} : Set U) ≤ Subgroup.normalizer (R' : Set U))
    (htwin : R ≠ R' → z = z' → ⁅R, R'⁆ = ⊥) (hne : R.map ψ ≠ R'.map ψ)
    (h2 : 2 ∣ Nat.card ↥(R.map ψ ⊓ R'.map ψ)) : ⁅R.map ψ, R'.map ψ⁆ = ⊥ := by
  classical
  have hinjR : ∀ x ∈ R, ψ x = 1 → x = 1 := fun x hx h1 =>
    Subgroup.mem_bot.mp (hRk ▸ Subgroup.mem_inf.mpr ⟨hx, h1⟩)
  have hinjR' : ∀ x ∈ R', ψ x = 1 → x = 1 := fun x hx h1 =>
    Subgroup.mem_bot.mp (hR'k ▸ Subgroup.mem_inf.mpr ⟨hx, h1⟩)
  have hzmap : IsUniqueInvolution (R.map ψ) (ψ z) := isUniqueInvolution_map_of_injOn ψ hinjR hz
  have hz'map : IsUniqueInvolution (R'.map ψ) (ψ z') :=
    isUniqueInvolution_map_of_injOn ψ hinjR' hz'
  have hz'm : ψ z' ∈ R.map ψ ⊓ R'.map ψ := mem_of_two_dvd_card hz'map inf_le_right h2
  have hψeq : ψ z = ψ z' :=
    ((hzmap.unique _ hz'm.1 hz'map.sq).resolve_left hz'map.ne_one).symm
  have hc_ker : z' * z⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, mul_inv_cancel]
  have hc_center : z' * z⁻¹ ∈ Subgroup.center U := hker hc_ker
  have hRN : R ≤ Subgroup.normalizer (R' : Set U) := by
    intro r hr
    have h1 : Commute r (z' * z⁻¹) := Subgroup.mem_center_iff.mp hc_center r
    have h2' : Commute r z' := by
      have := h1.mul_right (hz.commute_of_mem hr).symm
      rwa [show (z' * z⁻¹) * z = z' by group] at this
    exact hW' (Subgroup.mem_centralizer_singleton_iff.mpr h2')
  have hR'N : R' ≤ Subgroup.normalizer (R : Set U) := by
    intro r hr
    have h1 : Commute r (z' * z⁻¹) := Subgroup.mem_center_iff.mp hc_center r
    have h1' : Commute r z' := (hz'.commute_of_mem hr).symm
    have h2' : Commute r z := by
      have := (Commute.inv_right_iff.mpr h1).mul_right h1'
      rwa [show (z' * z⁻¹)⁻¹ * z' = z by group] at this
    exact hW (Subgroup.mem_centralizer_singleton_iff.mpr h2')
  have hle : ⁅R, R'⁆ ≤ R ⊓ R' :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hR'N)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hRN)
  rcases eq_or_ne z z' with hzz | hzz
  · have hRne : R ≠ R' := fun h => hne (by rw [h])
    rw [← Subgroup.map_commutator R R' ψ, htwin hRne hzz, Subgroup.map_bot]
  · have h3 : 3 ≤ Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      obtain ⟨k, hk⟩ := hF
      omega
    have hN : ((R ⊓ R').subgroupOf R).Normal := by
      rw [inf_comm, Subgroup.inf_subgroupOf_right]
      exact Subgroup.normal_subgroupOf_of_le_normalizer hRN
    have hNodd : Odd (Nat.card ↥((R ⊓ R').subgroupOf R)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      apply Nat.not_even_iff_odd.mp
      intro he
      have hz_mem : z ∈ R ⊓ R' := mem_of_two_dvd_card hz inf_le_left (even_iff_two_dvd.mp he)
      rcases hz'.unique z hz_mem.2 hz.sq with h | h
      · exact hz.ne_one h
      · exact hzz h
    have hbotN : (R ⊓ R').subgroupOf R = ⊥ :=
      CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 hF h3 eR _ hN hNodd
    have hbot : R ⊓ R' = ⊥ :=
      (disjoint_of_le_iff_left_eq_bot inf_le_left).mp (Subgroup.subgroupOf_eq_bot.mp hbotN)
    have hcomm_bot : ⁅R, R'⁆ = ⊥ := le_bot_iff.mp (hle.trans_eq hbot)
    rw [← Subgroup.map_commutator R R' ψ, hcomm_bot, Subgroup.map_bot]

theorem mem_normalizer_map_of_centralizer_le_normalizer [Finite U] (ψ : U →* X)
    (hker : ψ.ker ≤ Subgroup.center U) {R R' : Subgroup U} (hR'k : R' ⊓ ψ.ker = ⊥)
    {z z' : U} (hz : IsUniqueInvolution R z) (hz' : IsUniqueInvolution R' z')
    (hW : Subgroup.centralizer ({z} : Set U) ≤ Subgroup.normalizer (R : Set U))
    (hW' : Subgroup.centralizer ({z'} : Set U) ≤ Subgroup.normalizer (R' : Set U))
    {v : X} (hv : v ∈ R'.map ψ) (hvc : ¬ ∀ w ∈ R'.map ψ, v * w = w * v)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * ψ z = ψ z * v) :
    v ∈ Subgroup.normalizer ((R.map ψ : Subgroup X) : Set X) := by
  classical
  obtain ⟨u, huR', rfl⟩ := Subgroup.mem_map.mp hv
  have hker' : (ψ.comp R'.subtype).ker = ⊥ := by
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype, Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.mpr (by rw [inf_comm]; exact hR'k)
  have hinj : Function.Injective (ψ.comp R'.subtype) := (MonoidHom.ker_eq_bot_iff _).mp hker'
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    (isPGroup_zpowers_map_iff R'.subtype R'.subtype_injective ⟨u, huR'⟩).mpr
      ((isPGroup_zpowers_map_iff (ψ.comp R'.subtype) hinj ⟨u, huR'⟩).mp hv2)
  have hunc : ¬ ∀ w ∈ R', u * w = w * u := by
    intro h
    apply hvc
    rintro w ⟨r, hr, rfl⟩
    calc ψ u * ψ r = ψ (u * r) := (map_mul ψ u r).symm
      _ = ψ (r * u) := by rw [h r hr]
      _ = ψ r * ψ u := map_mul ψ r u
  have hc_ker : ⁅z, u⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hvz.symm
  have hcomm2 : Commute z (u * u) :=
    commute_mul_self_of_commutator_mem_center hz.sq (hker hc_ker)
  have huu1 : u * u ≠ 1 := by
    intro hsq
    rcases hz'.unique u huR' hsq with rfl | rfl
    · exact hunc fun w _ => by simp
    · exact hunc fun w hw => hz'.commute_of_mem hw
  have hz'u : z' ∈ Subgroup.zpowers (u * u) :=
    mem_zpowers_of_isUniqueInvolution hz' (R'.mul_mem huR' huR') huu1 (hu2.to_le
      (Subgroup.zpowers_le.mpr (mul_mem (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u))))
  have hzj : z ∈ Subgroup.centralizer ({z'} : Set U) := by
    have hz'C : z' ∈ Subgroup.centralizer ({z} : Set U) :=
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm2.symm)) hz'u
    rw [Subgroup.mem_centralizer_singleton_iff] at hz'C ⊢
    exact hz'C.symm
  have hcR' : ⁅z, u⁆ ∈ R' := by
    rw [commutatorElement_def]
    exact R'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hW' hzj) u).mp huR') (R'.inv_mem huR')
  have hc1 : ⁅z, u⁆ = 1 := by
    have hmem : ⁅z, u⁆ ∈ R' ⊓ ψ.ker := ⟨hcR', hc_ker⟩
    rwa [hR'k, Subgroup.mem_bot] at hmem
  have huN : u ∈ Subgroup.normalizer (R : Set U) := hW <|
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm
  exact mem_normalizer_map
    (fun d hd => (Subgroup.mem_normalizer_iff.mp huN d).mp hd)
    (fun d hd => by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) d).mp hd)

end Disconnected.AschTight

end CFSG.ClassicalInvolution
