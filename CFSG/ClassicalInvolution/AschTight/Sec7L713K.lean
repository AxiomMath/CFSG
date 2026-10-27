module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713J
public import CFSG.ClassicalInvolution.AschTight.Sec7L713E

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem case_three (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) (h67 : RCommute Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    {J₁ L J : Subgroup G} (hJ₁ : J₁ ∈ Ω) (hRJ₁ : R ≤ J₁) (hL : L ∈ Ω) (hTL : T ≤ L)
    (hJ : J ∈ Ω) {a : G} (ha : IsUniqueInvolution J a)
    (haW : a ∈ Subgroup.normalizer (W : Set G)) (haT : conjSub a T = T) {u r v t : G}
    (hu : Subgroup.zpowers u = R ⊓ W) (hrR : r ∈ R) (hrW : r ∉ W)
    (hv : Subgroup.zpowers v = T ⊓ W) (htT : t ∈ T) (htW : t ∉ W)
    (h1 : t⁻¹ * u * t * (u * v)⁻¹ ∈ OCW W) (h2 : r⁻¹ * v * r * (v * u)⁻¹ ∈ OCW W)
    (h3 : (bar (hR.2 hrR) * (bar haW * bar (hR.2 hrR) * (bar haW)⁻¹)) ^ 3 = 1)
    (hbt : bar (hT.2 htT) =
      bar (hR.2 hrR) * (bar haW * bar (hR.2 hrR) * (bar haW)⁻¹) * bar (hR.2 hrR)) :
    L = J ∨ L ∈ omegaStarNbr Ω J := by
  have hW2 := isPGroup_of_mem_WSet hW
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, hη, rfl⟩ := id hW
    exact habel η hη
  have hXN := normalizer_le_normalizer_OCW W
  have hrN := hR.2 hrR
  have htN := hT.2 htT
  have ha2 : a * a = 1 := ha.sq
  have huRW : u ∈ R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvTW : v ∈ T ⊓ W := hv ▸ Subgroup.mem_zpowers v
  have huW := (Subgroup.mem_inf.mp huRW).2
  have hvW := (Subgroup.mem_inf.mp hvTW).2
  have hconjW : ∀ g ∈ Subgroup.normalizer (W : Set G), ∀ w ∈ W, g⁻¹ * w * g ∈ W :=
    fun g hg w hw => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
      rwa [inv_inv] at this
  have htu : t⁻¹ * u * t = u * v :=
    eq_of_mul_inv_mem_OCW hW2 (hconjW t htN u huW) (W.mul_mem huW hvW) h1
  have hrv : r⁻¹ * v * r = v * u :=
    eq_of_mul_inv_mem_OCW hW2 (hconjW r hrN v hvW) (W.mul_mem hvW huW) h2
  obtain ⟨hJ₁W, hRWU, hRcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hR hJ₁ hRJ₁
  obtain ⟨hLW, -, hTcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT hL hTL
  have hrr : r * r ∈ W := (Subgroup.mem_inf.mp
    (mul_self_mem_of_relIndex_two (relIndex_eq_two_of_card inf_le_left hRcard) hrR)).2
  have hrv2 : r * v * r⁻¹ = v * u := by
    have hc := hWab _ hrr _ hvW
    calc r * v * r⁻¹ = r⁻¹ * (r * r * v) * (r * r)⁻¹ * r := by group
      _ = r⁻¹ * (v * (r * r)) * (r * r)⁻¹ * r := by rw [hc]
      _ = r⁻¹ * v * r := by group
      _ = v * u := hrv
  obtain ⟨k, hk, hov, htv, htv', ht2⟩ := quat_data hp hq hΩ h611 hW hT hL hTL hv htT htW
  have haTW : conjSub a (T ⊓ W) = T ⊓ W := by
    rw [conjSub_inf, haT, mem_normalizer_iff_conjSub_eq.mp haW]
  have hav : a * v * a⁻¹ ∈ Subgroup.zpowers v := by
    rw [hv, ← haTW]
    exact conj_mem_conjSub hvTW
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hav
  have hatT : a * t * a⁻¹ ∈ T := haT ▸ conj_mem_conjSub htT
  have hatW : a * t * a⁻¹ ∉ W := by
    intro h
    apply htW
    have := hconjW a haW _ h
    simpa [mul_assoc] using this
  have htC : t ∉ T ⊓ W := fun h => htW (Subgroup.mem_inf.mp h).2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, a * t * a⁻¹ = v ^ m * t := by
    rcases mem_or_mul_inv_mem_of_relIndex_two (relIndex_eq_two_of_card inf_le_left hTcard) htT
      htC hatT with h | h
    · exact absurd (Subgroup.mem_inf.mp h).2 hatW
    · rw [← hv] at h
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
      exact ⟨m, by rw [hm]; group⟩
  have hc2 : a * t * (a * t) = v ^ (m + 2 ^ (k - 1)) := by
    calc a * t * (a * t) = (a * t * a⁻¹) * (a * a) * t := by group
      _ = v ^ m * (t * t) := by rw [hm, ha2]; group
      _ = v ^ (m + 2 ^ (k - 1)) := by
        rw [ht2, zpow_add, show ((2 : ℤ) ^ (k - 1)) = ((2 ^ (k - 1) : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast]
  have hRa : conjSub a R ∈ DSet Ω W := ⟨RSet.conj hΩ.conjInvariant hR.1 a, by
    have := conjSub_le_normalizer hR.2 a
    rwa [mem_normalizer_iff_conjSub_eq.mp haW] at this⟩
  have hsRa : a * r * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hrR
  have hx : bar hrN * bar hrN = 1 := (bar_of_mem_DSet hp hΩ h611 hW hR hrR hrW).2.2
  have hconj1 : conjSub r L = conjSub a J₁ := by
    refine conjSub_eq_of_bar hp hΩ h611 habel h67 hW hT hRa hrN htT htW hsRa ?_ hL
      (hΩ.conjInvariant a J₁ hJ₁) hTL (conjSub_mono hRJ₁)
    change bar hrN * bar htN * (bar hrN)⁻¹ = bar haW * bar hrN * (bar haW)⁻¹
    rw [hbt]
    exact s3_conj_x hx
  have h2u : 2 ∣ orderOf u := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hRWU
    obtain ⟨n, hn⟩ :=
      ((isPGroup_of_mem_RSet hR.1).to_le (inf_le_left : R ⊓ W ≤ R)).exists_card_eq
    rw [← Nat.card_zpowers, hu, hn]
    rw [hn] at h4
    rcases n with _ | n
    · norm_num at h4
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨i, hi, hau⟩ := exists_odd_conj hrN haW hconj1 hLW hJ₁W hu hv hrv2 h2u
  have hα : bar haW * bar haW = 1 :=
    (bar_eq_one_iff (Subgroup.mul_mem _ haW haW)).mpr (by rw [ha2]; exact Subgroup.one_mem _)
  obtain ⟨j, x₁, hx₁, hrc⟩ := exists_conj_eq_mul hp hq hΩ habel h611 h67 hW hR hJ₁ hRJ₁ haW ha2
    htN hrR hrW hu hx h3 hα hbt
  have hWX : ∀ w ∈ W, w ∈ OCW W → w = 1 := fun w hw hwX =>
    eq_of_mul_inv_mem_OCW hW2 hw W.one_mem (by simpa using hwX)
  have hm2 := even_of_relations hWab hWX hk huW hvW h2u htu htv' hrv2 hi hau ha2 hc2 hx₁ hrc
    (hXN (Subgroup.mul_mem _ haW htN)) (hXN (Subgroup.le_normalizer huW))
  obtain ⟨g, hga, hg4, hgcl⟩ := exists_fixed_of_even hk hov htv ht2 ha2 he.symm hm hm2
  have hcl : Subgroup.closure ({v, t} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (Subgroup.mem_inf.mp hvTW).1
    · exact htT
  exact eq_or_mem_omegaStarNbr_of_fixed hp hq hΩ hJ hL ha (hTL (hcl hgcl)) hga hg4

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
