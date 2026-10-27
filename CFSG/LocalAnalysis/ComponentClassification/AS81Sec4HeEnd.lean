module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34OutPerfect
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ComponentClassification.AS81.HeEnd

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

section General

variable {G : Type*} [Group G] [Finite G]

theorem exists_rightConjugate_eq {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (hP : IsSylowOf p P K) (hP' : IsSylowOf p P' K) : ∃ x ∈ K, P' = rightConjugate P x := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨(d : G)⁻¹, K.inv_mem d.2, ?_⟩
  change _ = Subgroup.map (MulAut.conj (d : G)⁻¹⁻¹).toMonoidHom _
  rw [inv_inv, ← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem le_of_frattini {N L P H : Subgroup G} (hN : N ≤ normalizer (L : Set G))
    (hP : IsSylowOf 2 P L) (hLH : L ≤ H) (hPH : normalizer (P : Set G) ≤ H) : N ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn
  have hP'L : rightConjugate P n⁻¹ ≤ L := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h := (mem_normalizer_iff.mp (hN hn) _).mp (hP.le hx)
    simpa [mul_assoc] using h
  obtain ⟨ℓ, hℓ, heq⟩ := exists_rightConjugate_eq hP
    (isSylowOf_of_card hP'L (by rw [rightConjugate_card, hP.card_eq]))
  have h1 : rightConjugate P (ℓ * n) = P := by
    rw [← rightConjugate_mul, ← heq, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  have h2 := H.mul_mem (H.inv_mem (hLH hℓ)) (hPH ((rightConjugate_eq_self_iff P _).mp h1))
  simpa using h2

end General

section Endgame

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem normalizer_S₁_le (hQ : Sec4Q G A R g E F S₁ Q z) :
    normalizer (S₁ : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have hz : z ∈ centerIn S₁ := by rw [hQ.center_S₁]; exact mem_zpowers z
  have h1 : n * z * n⁻¹ ∈ centerIn S₁ := by
    refine mem_centerIn.mpr ⟨(mem_normalizer_iff.mp hn z).mp hz.1, ?_⟩
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S₁ := by
      have := (mem_normalizer_iff.mp (inv_mem hn) s).mp hs
      simpa using this
    have hc := mem_centralizer_iff.mp hz.2 _ hs'
    calc s * (n * z * n⁻¹) = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by rw [hc]
      _ = n * z * n⁻¹ * s := by group
  rw [hQ.center_S₁] at h1
  rw [mem_centralizer_singleton_iff]
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z h1 with h | h
  · refine absurd ?_ hQ.z_ne_one
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]

theorem normalizer_E_le (hQ : Sec4Q G A R g E F S₁ Q z) (hS₁E : S₁ ≤ normalizer (E : Set G))
    {H : Subgroup G} (hCH : centralizer ({z} : Set G) ≤ H)
    (hLE : AS76b.oUpperTwoPrime (normalizer (E : Set G)) ≤ H) :
    normalizer (E : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁L : S₁ ≤ AS76b.oUpperTwoPrime (normalizer (E : Set G)) := fun s hs => by
    obtain ⟨k, hk⟩ := hQ.sylow.isPGroup ⟨s, hs⟩
    exact AS76b.mem_oUpperTwoPrime (hS₁E hs) (n := k) (by simpa using congrArg Subtype.val hk)
  exact le_of_frattini (le_normalizer.trans (AS76b.normalizer_le_normalizer_oUpperTwoPrime _))
    (hQ.sylow.of_le hS₁L le_top) hLE ((normalizer_S₁_le hQ).trans hCH)

omit [Finite G] in
theorem rightConjugate_injective {X Y : Subgroup G} {n : G}
    (h : rightConjugate X n = rightConjugate Y n) : X = Y := by
  have h' := congrArg (fun U => rightConjugate U n⁻¹) h
  simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using h'

theorem normalizer_sup_le (hQ : Sec4Q G A R g E F S₁ Q z) (hRA : R ≤ A)
    (hS₁E : S₁ ≤ normalizer (E : Set G)) {H : Subgroup G} (hEH : normalizer (E : Set G) ≤ H) :
    normalizer ((E ⊔ F : Subgroup G) : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hQ.setting.frame
  have hL := hQ.setting.type
  set N := normalizer ((E ⊔ F : Subgroup G) : Set G) with hNdef
  have hconj : ∀ n ∈ N, ∀ X : Subgroup G, X ≤ E ⊔ F → IsElemAbelian 2 X → Nat.card X = 64 →
      rightConjugate X n = E ∨ rightConjugate X n = F := by
    intro n hn X hXS hXe hX64
    refine hF.eq_or_eq_of_isElemAbelian hRA hL (fun y hy => ?_)
      (AS76b.isElemAbelian_rightConjugate hXe n) (by rw [rightConjugate_card, hX64])
    rw [mem_rightConjugate_iff] at hy
    have h := (mem_normalizer_iff.mp (inv_mem hn) _).mp (hXS hy)
    simpa [mul_assoc] using h
  have hE := fun n hn => hconj n hn E le_sup_left hF.elemE hF.cardE
  have hFc := fun n hn => hconj n hn F le_sup_right hF.elemF hF.cardF
  intro n hn
  rcases hE n hn with h | h
  · exact hEH ((rightConjugate_eq_self_iff E n).mp h)
  · exfalso
    have hnF : rightConjugate F n = E := by
      rcases hFc n hn with h' | h'
      · exact h'
      · exact absurd (rightConjugate_injective (h.trans h'.symm)) hF.ne
    have hmem : ∀ m : ↥N, m ∈ (N ⊓ normalizer (E : Set G)).subgroupOf N ↔
        rightConjugate E m = E := fun m => by
      rw [mem_subgroupOf, mem_inf, rightConjugate_eq_self_iff]
      exact ⟨fun h => h.2, fun h => ⟨m.2, h⟩⟩
    have hidx : (N ⊓ normalizer (E : Set G)).relIndex N = 2 := by
      refine index_eq_two_iff.mpr ⟨⟨n, hn⟩, fun b => ?_⟩
      rw [hmem, hmem, coe_mul, ← rightConjugate_mul]
      change Xor (rightConjugate (rightConjugate E b) n = E) (rightConjugate E b = E)
      rcases hE b b.2 with hb | hb
      · rw [hb, h]
        exact Or.inr ⟨rfl, fun h' => hF.ne h'.symm⟩
      · rw [hb, hnF]
        exact Or.inl ⟨rfl, fun h' => hF.ne h'.symm⟩
    have hdvd : 2 ∣ S₁.relIndex N := by
      rw [← relIndex_mul_relIndex S₁ (N ⊓ normalizer (E : Set G)) N
        (le_inf hQ.sylowN.le hS₁E) inf_le_left, hidx]
      exact dvd_mul_left 2 _
    exact (isSylowOf_iff.mp hQ.sylowN).2.2 hdvd

theorem centralizer_A_eq (hQ : Sec4Q G A R g E F S₁ Q z) (hRA : R ≤ A)
    (hCE : centralizer (E : Set G) ≤ E) : centralizer (A : Set G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hQ.setting.frame
  have hEA : E ≤ A := (sup_eq_left.mpr hRA) ▸ hF.E_le
  have hCAE : centralizer (A : Set G) ≤ E := (centralizer_le hEA).trans hCE
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  exact hF.sylowR.eq_of_le hF.sylowR.le le_rfl (hE2.to_le hCAE)

theorem card_A (hQ : Sec4Q G A R g E F S₁ Q z) (hRA : R ≤ A)
    (hCA : centralizer (A : Set G) = R) : Nat.card A = 80640 := by
  have hF := hQ.setting.frame
  have hZ : (center ↥A).map A.subtype = R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hCA, mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val ((mem_center_iff.mp hy) ⟨a, ha⟩)
    · intro hx
      refine ⟨⟨x, hRA hx⟩, mem_center_iff.mpr fun a => Subtype.ext ?_, rfl⟩
      exact (mem_centralizer_iff.mp (hF.sylowR.le hx)) a a.2
  have hZc : Nat.card (center ↥A) = 4 := by
    rw [← card_map_of_injective A.subtype_injective, hZ, hF.cardR]
  have h := (center ↥A).card_eq_card_quotient_mul_card_subgroup
  rw [show Nat.card (↥A ⧸ center ↥A) = 20160 from card_rankTwoQuot_of_typeL34 hQ.setting.type,
    hZc] at h
  rw [h]

theorem le_A_of_perfect (hQ : Sec4Q G A R g E F S₁ Q z)
    (hRA : R ≤ A) (hCA : centralizer (A : Set G) = R) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPN : P ≤ normalizer (A : Set G)) : P ≤ A := by
  have hAp : Group.IsPerfect ↥A := ⟨hQ.setting.frame.quasisimple.1⟩
  have hAt : GrSLit.IsL34Type (↥A ⧸ center ↥A) := Or.inl ⟨by decide, hQ.setting.type⟩
  have h := GrSLit.L34Out.le_sup_centralizer_of_perfect hAp hAt hP hPN
  rwa [hCA, sup_eq_left.mpr hRA] at h

theorem centralizer_le_normalizer (hQ : Sec4Q G A R g E F S₁ Q z) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) : centralizer ({r} : Set G) ≤ normalizer (A : Set G) := by
  have hF := hQ.setting.frame
  have hstd := hF.base.hyp.standard
  intro c hc
  rw [← AS76b.normalizer_centralizer_eq hstd]
  exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded
    (AS76b.tightlyEmbedded_centralizer hstd) (hF.sylowR.le hr) hr1 (hF.elemR.2 r hr)
    (mem_centralizer_singleton_iff.mp hc)

theorem exists_mem_R (hQ : Sec4Q G A R g E F S₁ Q z) : ∃ r ∈ R, r ≠ 1 := by
  have hR : R ≠ ⊥ := by
    intro h
    have := hQ.setting.frame.cardR
    rw [h, card_bot] at this
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
  exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩

theorem inf_centralizer_R_eq (hQ : Sec4Q G A R g E F S₁ Q z)
    (hRA : R ≤ A) (hCA : centralizer (A : Set G) = R) {H : Subgroup G}
    (hAp : ⁅H ⊓ centralizer (R : Set G), H ⊓ centralizer (R : Set G)⁆ =
      H ⊓ centralizer (R : Set G))
    (hAc : Nat.card ↥(H ⊓ centralizer (R : Set G)) = 80640) :
    H ⊓ centralizer (R : Set G) = A := by
  obtain ⟨r, hr, hr1⟩ := exists_mem_R hQ
  have hle : H ⊓ centralizer (R : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hr)).trans
      (centralizer_le_normalizer hQ hr hr1))
  exact eq_of_le_of_card_ge (le_A_of_perfect hQ hRA hCA hAp hle)
    (by rw [card_A hQ hRA hCA, hAc])

theorem normalizer_A_le (hQ : Sec4Q G A R g E F S₁ Q z) (hRA : R ≤ A) {H : Subgroup G}
    (hAH : A ≤ H) (hSH : normalizer ((E ⊔ F : Subgroup G) : Set G) ≤ H) :
    normalizer (A : Set G) ≤ H :=
  le_of_frattini le_rfl ((sup_eq_left.mpr hRA) ▸ hQ.setting.frame.sylow) hAH hSH

theorem mem_normalizer_of_conj (hQ : Sec4Q G A R g E F S₁ Q z)
    (hRA : R ≤ A) (hCA : centralizer (A : Set G) = R) {r₁ r₂ k : G} (hr₁ : r₁ ∈ R)
    (hr₂ : r₂ ∈ R) (hr₂1 : r₂ ≠ 1) (hk : k * r₁ * k⁻¹ = r₂) : k ∈ normalizer (A : Set G) := by
  have hF := hQ.setting.frame
  have hAp : ⁅A, A⁆ = A := isPerfect_iff.mp ⟨hF.quasisimple.1⟩
  have hC : rightConjugate A k⁻¹ ≤ centralizer ({r₂} : Set G) := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have h := (mem_centralizer_iff.mp (hF.sylowR.le hr₁)) _ hy
    rw [mem_centralizer_singleton_iff, ← hk]
    calc y * (k * r₁ * k⁻¹) = k * ((k⁻¹ * y * k) * r₁) * k⁻¹ := by group
      _ = k * (r₁ * (k⁻¹ * y * k)) * k⁻¹ := by rw [h]
      _ = k * r₁ * k⁻¹ * y := by group
  have hP : ⁅rightConjugate A k⁻¹, rightConjugate A k⁻¹⁆ = rightConjugate A k⁻¹ := by
    simp only [rightConjugate]
    rw [← map_commutator, hAp]
  have hle := le_A_of_perfect hQ hRA hCA hP (hC.trans (centralizer_le_normalizer hQ hr₂ hr₂1))
  have heq : rightConjugate A k⁻¹ = A :=
    eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact inv_mem_iff.mp ((rightConjugate_eq_self_iff A _).mp heq)

theorem eq_top
    (hQ : Sec4Q G A R g E F S₁ Q z) (hs : IsSimpleGroup G)
    (hO2 : pCoreOf 2 (centralizer ({z} : Set G)) = Q) (hRA : R ≤ A)
    (hS₁E : S₁ ≤ normalizer (E : Set G)) (hCE : centralizer (E : Set G) ≤ E)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504)
    {H : Subgroup G} (hCH : centralizer ({z} : Set G) ≤ H)
    (hLE : AS76b.oUpperTwoPrime (normalizer (E : Set G)) ≤ H)
    (hinv : ∀ u ∈ H, orderOf u = 2 →
      (∃ c ∈ H, c * u * c⁻¹ = z) ∨ ∃ r ∈ R, r ≠ 1 ∧ ∃ c ∈ H, c * u * c⁻¹ = r)
    (hCr : ∀ r ∈ R, r ≠ 1 → Nat.card ↥(H ⊓ centralizer ({r} : Set G)) = 161280)
    (hAp : ⁅H ⊓ centralizer (R : Set G), H ⊓ centralizer (R : Set G)⁆ =
      H ⊓ centralizer (R : Set G))
    (hAc : Nat.card ↥(H ⊓ centralizer (R : Set G)) = 80640) : H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hQ.setting.frame
  have hCA := centralizer_A_eq hQ hRA hCE
  have hSH := normalizer_sup_le hQ hRA hS₁E (normalizer_E_le hQ hS₁E hCH hLE)
  have hAH : A ≤ H := (inf_centralizer_R_eq hQ hRA hCA hAp hAc) ▸ inf_le_left
  have hNA := normalizer_A_le hQ hRA hAH hSH
  have hzH : z ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  set T : Set G := insert z {r | r ∈ R ∧ r ≠ 1} with hTdef
  have hCT : ∀ t ∈ T, centralizer ({t} : Set G) ≤ H := by
    rintro t (rfl | ⟨hr, hr1⟩)
    · exact hCH
    · exact (centralizer_le_normalizer hQ hr hr1).trans hNA
  have hT : ∀ u ∈ H, orderOf u = 2 → ∃ t ∈ T, ∃ c ∈ H, c * u * c⁻¹ = t := by
    intro u hu hu2
    rcases hinv u hu hu2 with ⟨c, hc, h⟩ | ⟨r, hr, hr1, c, hc, h⟩
    · exact ⟨z, Set.mem_insert z _, c, hc, h⟩
    · exact ⟨r, Set.mem_insert_of_mem z ⟨hr, hr1⟩, c, hc, h⟩
  have hzr : ∀ r ∈ R, r ≠ 1 → ∀ k : G, k * z * k⁻¹ ≠ r := by
    intro r hr hr1 k hk
    have h1 : Nat.card (centralizer ({r} : Set G)) = 21504 := by
      rw [← hk, ← map_conj_centralizer, card_map_of_injective (MulAut.conj k).injective, hCz]
    have h2 := card_le_of_le (inf_le_right : H ⊓ centralizer ({r} : Set G) ≤ _)
    rw [hCr r hr hr1, h1] at h2
    omega
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, ∀ k : G, k * t * k⁻¹ = t' → ∃ c ∈ H, c * t * c⁻¹ = t' := by
    rintro t (rfl | ⟨hr, hr1⟩) t' (rfl | ⟨hr', hr1'⟩) k hk
    · exact ⟨1, H.one_mem, by group⟩
    · exact absurd hk (hzr t' hr' hr1' k)
    · refine absurd ?_ (hzr t hr hr1 k⁻¹)
      rw [← hk]
      group
    · exact ⟨k, hNA (mem_normalizer_of_conj hQ hRA hCA hr hr' hr1' hk), hk⟩
  have hcent : ∀ u ∈ H, orderOf u = 2 → centralizer ({u} : Set G) ≤ H := by
    intro u hu hu2 y hy
    obtain ⟨t, ht, c, hc, h⟩ := hT u hu hu2
    have hy' : c * y * c⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [← h, ← map_conj_centralizer]
      exact ⟨y, hy, rfl⟩
    have := H.mul_mem (H.mul_mem (H.inv_mem hc) (hCT t ht hy')) hc
    simpa [mul_assoc] using this
  have hev : Even (Nat.card H) := by
    refine even_iff_two_dvd.mpr ?_
    rw [← hQ.order_z, ← Subgroup.orderOf_mk z hzH]
    exact orderOf_dvd_natCard _
  refine HeSE.eq_top_of_fusion hs hF.elemR hF.cardR H hev (HeSE.fusion_of_reps H T hT hTT)
    hcent ?_
  intro S hSp hScard hSH' hHN
  have hS₁N : S₁ ≤ normalizer (S : Set G) := (hQ.le_centralizer.trans hCH).trans hHN
  have hSsyl : IsSylowOf 2 S ⊤ := isSylowOf_of_card le_top (by rw [hScard, card_top])
  have hjoin := hSsyl.eq_of_le le_sup_right le_top
    (hQ.sylow.isPGroup.to_sup_of_normal_right' hSp hS₁N)
  have hS₁S : S₁ = S := eq_of_le_of_card_ge (hjoin ▸ le_sup_left)
    (by rw [hScard, hQ.sylow.card_eq, card_top])
  have hS₁Q : S₁ ≤ Q := hO2 ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    hQ.le_centralizer (hS₁S ▸ hCH.trans hHN) hQ.sylow.isPGroup
  have hker : Q.subgroupOf S₁ = ⊤ := eq_top_iff.mpr fun x _ => hS₁Q x.2
  rcases hQ.quot with ⟨φ, hφ, hφk⟩ | ⟨φ, hφ, hφk⟩
  · obtain ⟨x, hx⟩ := hφ (DihedralGroup.r 1)
    have hx1 : x ∈ φ.ker := by rw [hφk, hker]; exact mem_top x
    rw [MonoidHom.mem_ker, hx] at hx1
    exact absurd hx1 (by decide)
  · obtain ⟨x, hx⟩ := hφ (DihedralGroup.r 1)
    have hx1 : x ∈ φ.ker := by rw [hφk, hker]; exact mem_top x
    rw [MonoidHom.mem_ker, hx] at hx1
    exact absurd hx1 (by decide)

end Endgame

end CFSG.ComponentClassification.AS81.HeEnd
