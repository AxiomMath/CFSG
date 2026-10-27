module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem sup_OCW_le_centralizer : W ⊔ OCW W ≤ Subgroup.centralizer (W : Set G) := by
  refine sup_le (fun x hx => ?_) (Thompson.OCW_le_centralizer W)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW y hy x hx

theorem inf_W_eq_x₁ : K ⊓ W = Subgroup.zpowers C.D.x₁ := by
  rw [C.D.h₁, C.hR]
  apply le_antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [← C.inf_S_eq_R]
    exact ⟨hx.1, C.hd.hWS hx.2⟩
  · exact inf_le_inf_right W C.hd.hR.2.1

theorem inf_W_eq_x₂ : K' ⊓ W = Subgroup.zpowers C.D.x₂ := by
  rw [C.D.h₂, C.hR']
  apply le_antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [← C.inf_S_eq_R']
    exact ⟨hx.1, C.hd.hWS hx.2⟩
  · exact inf_le_inf_right W C.hd.hR'.2.1

theorem conj_x₁_cases {y : G} (hyN : y ∈ Subgroup.normalizer (W : Set G))
    (hyK : conjSub y K = K) :
    y * C.D.x₁ * y⁻¹ = C.D.x₁ ∨ y * C.D.x₁ * y⁻¹ = C.D.x₁⁻¹ := by
  refine eq_or_eq_inv_of_conj_mem C.orderOf_x₁ ?_
  rw [← inf_W_eq_x₁ C]
  refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyN _).mp C.D.x₁_mem⟩
  have h := conj_mem_conjSub (n := y) C.x₁_mem_K
  rwa [hyK] at h

include C in
theorem acts_pm {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y) :
    (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) := by
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := C.le_normalizer_W hyS
  have hK : conjSub y K = K := by
    have h := C.fix_of_trivMu hyN hT C.D.F.ρ
    rwa [C.hK] at h
  have h1 := conj_x₁_cases C hyN hK
  have hsM : C.D.F.ρ₃.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.D.F.ρ₃.hr
  obtain ⟨n, hnd⟩ : ∃ n, y * C.D.F.ρ₃.r * y⁻¹ * C.D.F.ρ₃.r⁻¹ = n := ⟨_, rfl⟩
  have hn : n ∈ W ⊔ OCW W := hnd ▸ hT _ hsM
  have hnc := sup_OCW_le_centralizer C hn
  have hys : y * C.D.F.ρ₃.r * y⁻¹ = n * C.D.F.ρ₃.r := by rw [← hnd]; group
  have hx13 : C.D.x₁ * C.D.x₃ ∈ W := W.mul_mem C.D.x₁_mem C.D.x₃_mem
  have key : (y * C.D.x₁ * y⁻¹) * (y * C.D.x₃ * y⁻¹) =
      n * (C.D.F.ρ₃.r * (y * C.D.x₁ * y⁻¹) * C.D.F.ρ₃.r⁻¹) * n⁻¹ := by
    calc (y * C.D.x₁ * y⁻¹) * (y * C.D.x₃ * y⁻¹) = y * (C.D.x₁ * C.D.x₃) * y⁻¹ := by group
      _ = y * (C.D.F.ρ₃.r * C.D.x₁ * C.D.F.ρ₃.r⁻¹) * y⁻¹ := by rw [C.D.s₁]
      _ = (y * C.D.F.ρ₃.r * y⁻¹) * (y * C.D.x₁ * y⁻¹) * (y * C.D.F.ρ₃.r * y⁻¹)⁻¹ := by group
      _ = (n * C.D.F.ρ₃.r) * (y * C.D.x₁ * y⁻¹) * (n * C.D.F.ρ₃.r)⁻¹ := by rw [hys]
      _ = n * (C.D.F.ρ₃.r * (y * C.D.x₁ * y⁻¹) * C.D.F.ρ₃.r⁻¹) * n⁻¹ := by group
  have hconj : ∀ a b : ℤ, y * (C.D.x₁ ^ a * C.D.x₃ ^ b) * y⁻¹ =
      (y * C.D.x₁ * y⁻¹) ^ a * (y * C.D.x₃ * y⁻¹) ^ b := fun a b => by
    rw [conj_zpow, conj_zpow]
    group
  rcases h1 with h1 | h1
  · left
    have e := key
    rw [h1, C.D.s₁, conj_eq_of_mem_centralizer hnc hx13] at e
    have h3 : y * C.D.x₃ * y⁻¹ = C.D.x₃ := mul_left_cancel e
    intro w hw
    obtain ⟨a, b, rfl⟩ := C.exists_nf hw
    rw [hconj, h1, h3]
  · right
    have e := key
    have e' : C.D.F.ρ₃.r * C.D.x₁⁻¹ * C.D.F.ρ₃.r⁻¹ = (C.D.x₁ * C.D.x₃)⁻¹ := by
      rw [← C.D.s₁]
      group
    rw [h1, e', conj_eq_of_mem_centralizer hnc (W.inv_mem hx13)] at e
    have h3 : y * C.D.x₃ * y⁻¹ = C.D.x₃⁻¹ := by
      calc y * C.D.x₃ * y⁻¹ = C.D.x₁ * (C.D.x₁⁻¹ * (y * C.D.x₃ * y⁻¹)) := by group
        _ = C.D.x₁ * (C.D.x₁ * C.D.x₃)⁻¹ := by rw [e]
        _ = C.D.x₃⁻¹ := by rw [C.D.comm13.eq]; group
    intro w hw
    obtain ⟨a, b, rfl⟩ := C.exists_nf hw
    rw [hconj, h1, h3, inv_zpow', inv_zpow', mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (C.D.comm13.zpow_zpow (-a) (-b)).eq

include C in
theorem piG_eq_one_of_trivMu {m : G} (hm : m ∈ MGrp Ω W) (hT : S24B.TrivMu Ω W m) :
    Thompson.piG W m = 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24.piG_eq_one_of_trivMu_of C.D.φ hm hT

include C in
theorem conjSub_eq_of_conj {L : Subgroup G} (hL : L ∈ Ω) {x m : G} (hx : x ∈ L)
    (o : orderOf x = 4) (h : m⁻¹ * x * m = x ∨ m⁻¹ * x * m = x⁻¹) : conjSub m L = L := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24.conjSub_eq_of_conj_of C.D.c.hΩ hL hx o h

include C in
theorem not_inv_of_mem_MGrp {m : G} (hm : m ∈ MGrp Ω W) (hinv : ∀ w ∈ W, m * w * m⁻¹ = w⁻¹) :
    False := by
  have hmN := Thompson.MGrp_le_normalizer Ω W hm
  have hinv' := inv_conj_of_inv hinv
  have h1 : conjSub m C.D.F.ρ.K = C.D.F.ρ.K :=
    conjSub_eq_of_conj C C.D.F.ρ.hK (by rw [C.hK]; exact C.x₁_mem_K) C.orderOf_x₁
      (Or.inr (hinv' _ C.D.x₁_mem))
  have h2 : conjSub m C.D.F.ρ'.K = C.D.F.ρ'.K :=
    conjSub_eq_of_conj C C.D.F.ρ'.hK (by rw [C.hK']; exact C.x₂_mem_K') C.orderOf_x₂
      (Or.inr (hinv' _ C.D.x₂_mem))
  have h3 : conjSub m C.D.F.ρ₃.K = C.D.F.ρ₃.K :=
    conjSub_eq_of_conj C C.D.F.ρ₃.hK C.x₃_mem_J C.orderOf_x₃ (Or.inr (hinv' _ C.D.x₃_mem))
  have hT := C.trivMu_of_fix hmN h1 h2 h3
  have hmW : m ∈ W ⊔ OCW W := (Thompson.piG_eq_one_iff hmN).mp (piG_eq_one_of_trivMu C hm hT)
  have e1 := conj_eq_of_mem_centralizer (sup_OCW_le_centralizer C hmW) C.D.x₁_mem
  rw [hinv _ C.D.x₁_mem] at e1
  have e2 : C.D.x₁ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← e1]
    exact inv_mul_cancel _
  have := orderOf_dvd_of_pow_eq_one e2
  rw [C.orderOf_x₁] at this
  omega

include C in
theorem not_mem_sZero {c : G} (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c ∉ sZero Ω W S := by
  rintro ⟨-, m, hm, h⟩
  exact not_inv_of_mem_MGrp C hm fun w hw => (h w hw).symm.trans (hinv w hw)

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G]
variable [Finite G] {Ω : Set (Subgroup G)}

theorem inv_of_member (hΩ : HypOmegaMod Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {zL : G} (hzL : IsUniqueInvolution L zL) {Q : Subgroup G} (hQ : IsSylow2In Q L)
    (h8 : Nat.card ↥Q = 8) :
    ∀ Q₁ : Subgroup G, IsSylow2In Q₁ L → ∀ b ∈ Q₁, orderOf b = 4 →
      ∀ g ∈ Q₁, g ∉ Subgroup.zpowers b → g * b * g⁻¹ = b⁻¹ := by
  intro Q₁ hQ₁ b hb ob g hg hgU
  have hquat := hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hL hQ₁)
  have hz₁ := AscL62.isUniqueInvolution_of_le hzL hQ₁.1 (T7C.mem_of_isSylow2In hΩ hL hQ₁ hzL)
  have hcard : Nat.card ↥Q₁ = 2 * Nat.card ↥(Subgroup.zpowers b) := by
    rw [hQ₁.natCard_eq hQ, h8, Nat.card_zpowers, ob]
  exact AscL62.conj_eq_inv_of_not_mem hquat hz₁ (Subgroup.zpowers_le.mpr hb) inferInstance hcard
    hg hgU (Subgroup.mem_zpowers b)

theorem orderOf_of_member (hΩ : HypOmegaMod Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {zL : G} (hzL : IsUniqueInvolution L zL) {Q : Subgroup G} (hQ : IsSylow2In Q L)
    {x : G} (hxQ : x ∈ Q) (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x)) :
    ∀ g ∈ Q, g ∉ Subgroup.zpowers x → orderOf g = 4 := by
  intro g hg hgU
  have hquat := hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hL hQ)
  have hz := AscL62.isUniqueInvolution_of_le hzL hQ.1 (T7C.mem_of_isSylow2In hΩ hL hQ hzL)
  have hgg : g * g = zL := AscL62.sq_eq_of_not_mem hquat hz (Subgroup.zpowers_le.mpr hxQ)
    inferInstance hcard hg hgU
  have h4 : orderOf g = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hgg]
      exact hzL.ne_one
    · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hgg]
      exact hzL.sq
  rw [h4]
  norm_num

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem exists_conj_W {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) : ∃ h : G, conjSub h W = W₁ := by
  obtain ⟨η, hηG, hWη⟩ := id C.hd.hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup G) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup G) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have hP : PartIHyp Ω := ⟨C.hyp, C.partI.cls, C.partI.aEmpty⟩
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := C.trans K₁ hK₁
    obtain ⟨g₂, rfl⟩ := C.trans J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := Disconnected.AschTight.Sec7.l6_12_mod G Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, -⟩ | h2
  · have hMS₀ : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup G)}, U) ≤
        (S₀ : Subgroup G) := iSup₂_le fun U hU => hU.2
    have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
    obtain ⟨η₁, ⟨S₁, hS₁, hinv₁⟩, rfl⟩ := hW₁
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₁ S₀
    have hinv₁' : ∀ s ∈ (S₀ : Subgroup G), ∀ U ∈ conjSub x '' η₁,
        conjSub s U ∈ conjSub x '' η₁ := by
      intro s hs U hU
      obtain ⟨U₀, hU₀, rfl⟩ := hU
      have hs' : x⁻¹ * s * x ∈ (S₁ : Subgroup G) := by
        rw [← hx, mem_conjSub_iff] at hs
        exact hs
      refine ⟨conjSub (x⁻¹ * s * x) U₀, hinv₁ _ hs' U₀ hU₀, ?_⟩
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    have hη₁' : conjSub x '' η₁ ∈ etaG Ω := by
      refine ⟨S₀, ?_, hinv₁'⟩
      have := conjSub_image_mem_etaSet C.hyp.conjInvariant hS₁ x
      rwa [hx] at this
    have hη₁eq : conjSub x '' η₁ = η₀ :=
      huniq _ hη₁' fun m hm U hU => hinv₁' m (hMS₀ hm) U hU
    refine ⟨x⁻¹, ?_⟩
    have e : conjSub x (⨆ U ∈ η₁, U) = W := by
      have e1 : conjSub x (⨆ U ∈ η₁, U) = ⨆ U ∈ conjSub x '' η₁, U := by
        rw [conjSub_iSup₂, iSup_image]
      rw [e1, hη₁eq, ← hηeq, hWη]
    rw [← e, conjSub_inv_conjSub]
  · exact (C.not_alt_two hWS₀ h2).elim

theorem inv_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w = 1 ∨ w = z ∨ w = C.D.F.j ∨ w = z * C.D.F.j := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.mul_nf] at h2
  obtain ⟨h1, h3⟩ := C.eq_one_of_nf _ _ h2
  have ha := C.four_dvd_of_x₁ h1
  have hb := C.four_dvd_of_x₃ h3
  have hx₁ : ∀ c : ℤ, C.D.x₁ ^ c = C.D.x₁ ^ (c % 4) := fun c => by
    have e := zpow_mod_orderOf C.D.x₁ c
    rw [C.orderOf_x₁] at e
    exact_mod_cast e.symm
  have hx₃ : ∀ c : ℤ, C.D.x₃ ^ c = C.D.x₃ ^ (c % 4) := fun c => by
    have e := zpow_mod_orderOf C.D.x₃ c
    rw [C.orderOf_x₃] at e
    exact_mod_cast e.symm
  have hz2 : C.D.x₁ ^ (2 : ℤ) = z := by rw [zpow_two, ← pow_two, C.x₁_sq]
  have hj2 : C.D.x₃ ^ (2 : ℤ) = C.D.F.j := by rw [zpow_two, ← pow_two, C.x₃_sq]
  have ha' : a % 4 = 0 ∨ a % 4 = 2 := by omega
  have hb' : b % 4 = 0 ∨ b % 4 = 2 := by omega
  rw [hx₁ a, hx₃ b]
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb']
  · left; simp
  · right; right; left; rw [zpow_zero, one_mul, hj2]
  · right; left; rw [zpow_zero, mul_one, hz2]
  · right; right; right; rw [hz2, hj2]

include C in
theorem exists_normalizer_conj_z {w : G} (hw : w ∈ W) (h2 : w * w = 1) (h1 : w ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (W : Set G), g * z * g⁻¹ = w := by
  have hrN := C.D.F.ρ.r_mem_normalizer
  have hsN := C.D.F.ρ₃.r_mem_normalizer
  have hzj : z * C.D.F.j = C.D.F.j * z := by
    have := Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW z C.hd.hzW
      C.D.F.j (by rw [← C.x₃_sq]; exact W.pow_mem C.D.x₃_mem 2)
    exact this
  have hrz : C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹ = z :=
    C.hzK.conj_eq (conjSub_eq_self_of_mem C.r_mem_K)
  have hrj : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
    rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]
  rcases inv_W C hw h2 with h | h | h | h
  · exact absurd h h1
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨C.D.F.ρ.r * C.D.F.ρ₃.r, Subgroup.mul_mem _ hrN hsN, ?_⟩
    calc C.D.F.ρ.r * C.D.F.ρ₃.r * z * (C.D.F.ρ.r * C.D.F.ρ₃.r)⁻¹
        = C.D.F.ρ.r * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) * C.D.F.ρ.r⁻¹ := by group
      _ = (C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹) := by
          rw [C.s_conj_z]; group
      _ = z * (C.D.F.j * z) := by rw [hrz, hrj]
      _ = w := by rw [h, ← hzj, ← mul_assoc, C.hzK.sq, one_mul]
  · exact ⟨C.D.F.ρ₃.r, hsN, by rw [h, C.s_conj_z]⟩

include C in
theorem twin_cases {h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G)) :
    (conjSub h K = K ∧ conjSub h K' = K') ∨ (conjSub h K = K' ∧ conjSub h K' = K) := by
  have hΩ := C.hyp
  have hzh : h * z * h⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    rw [hh]
    group
  have hK₁ : conjSub h K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant h K C.mem, z, C.hzK, by have := C.hzK.conj h; rwa [hzh] at this⟩
  have hK'₁ : conjSub h K' ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant h K' C.hK'tw.1, z, C.hzK, by have := C.hzK'.conj h; rwa [hzh] at this⟩
  rw [C.twinSet_eq] at hK₁ hK'₁
  have hne : conjSub h K ≠ conjSub h K' := fun e => C.hne ((conjSub_inj h).mp e).symm
  rcases hK₁ with h1 | h1 <;> rcases hK'₁ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

include C in
theorem exists_centralizer_conj_W {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G), conjSub h W = W₁ := by
  obtain ⟨h, rfl⟩ := exists_conj_W C hW₁
  rw [mem_conjSub_iff] at hzW₁
  have h2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [C.hzK.sq]; group
  have h1 : h⁻¹ * z * h ≠ 1 := by
    intro e
    apply C.hzK.ne_one
    calc z = h * (h⁻¹ * z * h) * h⁻¹ := by group
      _ = 1 := by rw [e]; group
  obtain ⟨g, hgN, hg⟩ := exists_normalizer_conj_z C hzW₁ h2 h1
  refine ⟨h * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * g * z = h * (g * z * g⁻¹) * g := by group
      _ = h * (h⁻¹ * z * h) * g := by rw [hg]
      _ = z * (h * g) := by group
  · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hgN]

include C in
theorem mem_sup_of_W1 {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) {v : G}
    (hv : v ∈ W₁) (hv2 : v * v = 1) : v ∈ K ⊔ K' := by
  obtain ⟨h, hh, rfl⟩ := exists_centralizer_conj_W C hW₁ hzW₁
  rw [mem_conjSub_iff] at hv
  have hw2 : (h⁻¹ * v * h) * (h⁻¹ * v * h) = 1 := by
    calc (h⁻¹ * v * h) * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h := by group
      _ = 1 := by rw [hv2]; group
  have hmem := C.cmSup hh (C.mem_sup_of_mul_self hv hw2)
  have e : h * (h⁻¹ * v * h) * h⁻¹ = v := by group
  rwa [e] at hmem

include C in
theorem mem_sup_of_conj_z {g : G} (hne : g * z * g⁻¹ ≠ z)
    (hcomm : (g * z * g⁻¹) * C.D.F.ρ.r = C.D.F.ρ.r * (g * z * g⁻¹)) :
    g * z * g⁻¹ ∈ K ⊔ K' := by
  have hΩ : HypOmegaMod Ω := C.hyp
  have hK : K ∈ Ω := C.mem
  have hL : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzL : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := C.hzK.conj g
  have hLK : conjSub g K ≠ K := by
    intro e
    rw [e] at hzL
    exact hne (hzL.eq C.hzK)
  have hrK : C.D.F.ρ.r ∈ K := C.r_mem_K
  have hor : orderOf C.D.F.ρ.r = 4 :=
    orderOf_of_member hΩ hK C.hzK C.hRsyl C.x₁_mem_R C.card_R C.D.F.ρ.r C.r_mem_R
      C.r_not_mem_zpowers
  have hnc : ¬ ∀ w ∈ K, C.D.F.ρ.r * w = w * C.D.F.ρ.r := by
    intro h
    have e := h _ C.x₁_mem_K
    have e2 : C.D.x₁⁻¹ = C.D.x₁ := by
      rw [← C.D.r₁, e]; group
    have e3 : C.D.x₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e2]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₁] at this
    omega
  have hr2 : IsPGroup 2 ↥(Subgroup.zpowers C.D.F.ρ.r) := T7A.isPGroup_zpowers_of_orderOf_four hor
  have hrN : C.D.F.ρ.r ∈ Subgroup.normalizer (conjSub g K : Set G) :=
    hΩ.omega5 _ hL K hK hLK _ hzL _ hrK hnc hr2 hcomm.symm
  have hU : Subgroup.zpowers C.D.F.ρ.r ∈ USet Ω := by
    refine mem_USet_of_natCard hK C.hRsyl (Subgroup.zpowers_le.mpr C.r_mem_R) inferInstance ?_
    simp [C.h8, Nat.card_zpowers, hor]
  have hKstar : K ∈ omegaStarNbr Ω (conjSub g K) :=
    ⟨hK, hLK.symm, _, hU, Subgroup.zpowers_le.mpr hrK, Subgroup.zpowers_le.mpr hrN⟩
  obtain ⟨W₁, hW₁, R₁, hR₁, T₁, hT₁, hR₁L, hT₁K⟩ :=
    Thompson.exists_W_of_mem_omegaStarNbr hΩ hL hKstar
  have hzhW : g * z * g⁻¹ ∈ W₁ :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hL hR₁ hR₁L hzL).2
  have hzW : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT₁ hT₁K C.hzK).2
  exact mem_sup_of_W1 C hW₁ hzW hzhW hzL.sq

include C in
theorem exists_sylow_pair_of_le {Y : Subgroup G} (hY : IsPGroup 2 Y) (hYK : Y ≤ K ⊔ K') :
    ∃ R₂ R₂' : Subgroup G, IsSylow2In R₂ K ∧ IsSylow2In R₂' K' ∧ Commutes R₂ R₂' ∧
      Y ≤ R₂ ⊔ R₂' := by
  have hΩ : HypOmegaMod Ω := C.hyp
  have hK : K ∈ Ω := C.mem
  have hK'Ω : K' ∈ Ω := C.hK'tw.1
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ :=
    T7A.exists_commuting_sylow_twin hΩ hK hK'Ω C.hne C.hzK C.hzK'
  have hQ₀ := T7A.isSylow2In_sup_of_twin hΩ hK hK'Ω C.hne C.hzK C.hzK' hR₀ hR₀' hc₀
  obtain ⟨P, hP, hYP⟩ := IsSylow2In.exists_ge hY hYK
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hK C.hne C.hzK' C.hzK
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω C.hne.symm C.hzK C.hzK'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  refine ⟨conjSub g R₀, conjSub g R₀', ?_, ?_, hc₀.conjSub g, ?_⟩
  · have := hR₀.conj g
    rwa [hgK] at this
  · have := hR₀'.conj g
    rwa [hgK'] at this
  · rw [← T7A.conjSub_sup_eq, hg]
    exact hYP

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
