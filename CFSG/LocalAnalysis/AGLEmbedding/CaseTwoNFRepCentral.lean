module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFThreeReps
import CFSG.LocalAnalysis.AGLEmbedding.Sp48OrbitOne

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.rep_central (h : D1PhaseThree p P M H R) (hR3 : IsPGroup 3 R)
    (hZ3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ζ ^ 3 = 1 → ζ = 1)
    {z w : G} (hzR : z ∈ R) (hz3 : z ^ 3 = 1) (hRz : ∀ y ∈ R, y * z = z * y)
    (hwR : w ∈ R) (hw3 : w ^ 3 = 1) (hRw : ∀ y ∈ R, y * w = w * y)
    (hwz : w ∉ Subgroup.zpowers z)
    (hrk : ∀ E : Subgroup G, E ≤ R → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hnC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      mbar M z (h.le_M hzR) ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {r : G} (hrR : r ∈ R)
    (hrL : mbar M r (h.le_M hrR) ∈ barM M L)
    (hrc : (mbar M r (h.le_M hrR))⁻¹ * mbar M z (h.le_M hzR) ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    r ^ 3 = 1 ∧ ∀ y ∈ R, y * r = r * y := by
  have hRM : R ≤ M := h.le_M
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  set zb := mbar M z (hRM hzR) with hzb
  set rb := mbar M r (hRM hrR) with hrb
  have hzb3 : zb ^ 3 = 1 := by rw [hzb, ← mbar_pow, ← mbar_one]; congr 1
  have hthree : ∀ x ∈ R, ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hR3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hthreeb : ∀ x (hx : x ∈ R), ∃ k : ℕ, (mbar M x (hRM hx)) ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hthree x hx
    exact ⟨k, by rw [← mbar_pow, ← mbar_one]; congr 1⟩
  obtain ⟨k₀, hk₀⟩ := hthreeb r hrR
  have hrzc : Commute rb zb := by
    show rb * zb = zb * rb
    rw [hrb, hzb, ← mbar_mul, ← mbar_mul]
    congr 1
    exact hRz r hrR
  have hrb3 : rb ^ 3 = 1 := rep_pow_p (hZ3 L hL) hrL hk₀ hzb3 hrzc hrc
  have hr3 : r ^ 3 = 1 := eq_of_mbar_eq_p hp3 hp32 hRM hR3 (R.pow_mem hrR 3) R.one_mem (by
    rw [mbar_pow (hRM hrR) 3, ← hrb, hrb3, mbar_one])
  refine ⟨hr3, fun y hy => ?_⟩
  have hyn : ∀ n : ℕ, y ^ n ∈ R := fun n => R.pow_mem hy n
  have hynz : ∀ n : ℕ, y ^ n * z = z * y ^ n := fun n => hRz _ (hyn n)
  have hrn : ∀ n : ℕ, y ^ n * r * (y ^ n)⁻¹ ∈ R := fun n =>
    R.mul_mem (R.mul_mem (hyn n) hrR) (R.inv_mem (hyn n))
  set ρ : ℕ → ↥M ⧸ CFSG.pCore 2 ↥M := fun n => mbar M (y ^ n * r * (y ^ n)⁻¹) (hRM (hrn n))
    with hρ
  set Lb : ℕ → Subgroup G := fun n => L.map (MulAut.conj (y ^ n)).toMonoidHom with hLb
  set A : ℕ → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun n => barM M (Lb n) with hA
  have hdat : ∀ n : ℕ, IsWeakSBlock M (pCoreOf 2 H) (Lb n) ∧ ρ n ∈ A n ∧
      (ρ n)⁻¹ * zb ∈ Subgroup.centralizer (A n : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun n =>
    D1PhaseThree.rep_conj h hzR hrR (hyn n) (hynz n) hL hrL hrc
  have hρ0 : ρ 0 = rb := by simp only [hρ, pow_zero, one_mul, inv_one, mul_one]; rfl
  have hA0 : A 0 = barM M L := by
    simp only [hA, hLb, pow_zero, map_one]
    congr 1
    ext x
    simp
  have hcomp : ∀ n, IsComponentOf (A n) ⊤ := fun n => (hdat n).1.component
  have hcen : ∀ m n, A m ≠ A n → A m ≤ Subgroup.centralizer (A n : Set _) := fun m n hmn =>
    le_centralizer_of_component_ne (hcomp m) (hcomp n) hmn
  have hrepeq : ∀ m n, A m = A n → y ^ m * r * (y ^ m)⁻¹ = y ^ n * r * (y ^ n)⁻¹ := by
    intro m n hmn
    have hm := hdat m
    have hn := hdat n
    rw [hmn] at hm
    obtain ⟨km, hkm⟩ := hthreeb _ (hrn m)
    obtain ⟨kn, hkn⟩ := hthreeb _ (hrn n)
    exact eq_of_mbar_eq_p hp3 hp32 hRM hR3 (hrn m) (hrn n)
      (rep_unique_p (hZ3 _ hn.1) hm.2.1 hn.2.1 hkm hkn hm.2.2 hn.2.2)
  by_cases hN : A 1 = A 0
  · have := hrepeq 1 0 hN
    simp only [pow_one, pow_zero, one_mul, inv_one, mul_one] at this
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [this]
  exfalso
  have key1 : y * r * y⁻¹ = r → False := by
    intro hyr
    have h1 : ρ 1 = rb := by
      simp only [hρ, pow_one]
      congr 1
    have hrA1 : rb ∈ A 1 := h1 ▸ (hdat 1).2.1
    have hrC : rb ∈ Subgroup.centralizer (A 0 : Set _) := hcen 1 0 hN hrA1
    apply hnC L hL
    rw [← hA0]
    have := Subgroup.mul_mem _ hrC (hA0 ▸ hrc)
    simpa using this
  have key2 : y ^ 2 * r * (y ^ 2)⁻¹ = r → False := by
    intro hyr
    obtain ⟨k, hk⟩ := hthree y hy
    have hmem := mem_zpowers_sq hk
    have hc2 : Commute (y ^ 2) r := by
      show y ^ 2 * r = r * y ^ 2
      calc y ^ 2 * r = y ^ 2 * r * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = r * y ^ 2 := by rw [hyr]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc : Commute y r := hn ▸ hc2.zpow_left n
    apply key1
    rw [hc.eq, mul_inv_cancel_right]
  have hA20 : A 2 ≠ A 0 := fun h20 => key2 (by
    have := hrepeq 2 0 h20
    simpa using this)
  have hA21 : A 2 ≠ A 1 := fun h21 => key1 (by
    have h := hrepeq 2 1 h21
    simp only [pow_one] at h
    have e : y * r * y⁻¹ = y⁻¹ * (y ^ 2 * r * (y ^ 2)⁻¹) * y := by group
    rw [e, h]; group)
  have hA31 : A 3 ≠ A 1 := fun h31 => key2 (by
    have h := hrepeq 3 1 h31
    simp only [pow_one] at h
    have e : y ^ 2 * r * (y ^ 2)⁻¹ = y⁻¹ * (y ^ 3 * r * (y ^ 3)⁻¹) * y := by group
    rw [e, h]; group)
  have hA32 : A 3 ≠ A 2 := fun h32 => key1 (by
    have h := hrepeq 3 2 h32
    have e : y * r * y⁻¹ = (y ^ 2)⁻¹ * (y ^ 3 * r * (y ^ 3)⁻¹) * y ^ 2 := by group
    rw [e, h]; group)
  have hρp : ∀ n, (ρ n) ^ 3 = 1 := fun n => by
    simp only [hρ]
    rw [← mbar_pow, ← mbar_one]
    congr 1
    rw [conj_pow, hr3, mul_one, mul_inv_cancel]
  have hρn : ∀ n, ρ n ∉ Subgroup.centralizer (A n : Set _) := fun n hc => by
    apply hnC _ (hdat n).1
    have := Subgroup.mul_mem _ hc (hdat n).2.2
    simpa using this
  have hT : ThreeReps (A 0) (A 1) (A 2) (ρ 0) (ρ 1) (ρ 2) :=
    { c01 := hcen 0 1 (Ne.symm hN), c02 := hcen 0 2 (Ne.symm hA20), c12 := hcen 1 2 (Ne.symm hA21)
      z0 := hZ3 _ (hdat 0).1, z1 := hZ3 _ (hdat 1).1, z2 := hZ3 _ (hdat 2).1
      m0 := (hdat 0).2.1, m1 := (hdat 1).2.1, m2 := (hdat 2).2.1
      p0 := hρp 0, p1 := hρp 1, p2 := hρp 2
      n0 := hρn 0, n1 := hρn 1, n2 := hρn 2 }
  set r' : ℕ → G := fun n => y ^ n * r * (y ^ n)⁻¹ with hr'
  have hcommG : ∀ m n, A m ≠ A n → r' m * r' n = r' n * r' m := fun m n hmn =>
    commute_of_mbar_p hp3 hp32 hRM hR3 (hrn m) (hrn n)
      ((Subgroup.mem_centralizer_iff.mp (hcen m n hmn (hdat m).2.1) _ (hdat n).2.1).symm)
  have hr'3 : ∀ n, r' n ^ 3 = 1 := fun n => by
    simp only [hr']; rw [conj_pow, hr3, mul_one, mul_inv_cancel]
  set F := Subgroup.zpowers (r' 0) ⊔ Subgroup.zpowers (r' 1) ⊔ Subgroup.zpowers (r' 2) with hF
  have hFR : F ≤ R := sup_le (sup_le ((Subgroup.zpowers_le).mpr (hrn 0))
    ((Subgroup.zpowers_le).mpr (hrn 1))) ((Subgroup.zpowers_le).mpr (hrn 2))
  have hzc : ∀ (a b : G), a * b = b * a →
      Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro a b hab
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute b a from hab.symm) n)).eq
  have hFel : IsElemAbelian 3 F := by
    refine isElemAbelian_sup_zpowers_of_mem_centralizer
      (isElemAbelian_sup_zpowers_of_mem_centralizer (isElemAbelian_zpowers_three (hr'3 0))
        (Subgroup.le_centralizer_iff.mp (hzc _ _ (hcommG 0 1 (Ne.symm hN)))
          (Subgroup.mem_zpowers _)) (hr'3 1))
      (Subgroup.le_centralizer_iff.mp (sup_le (hzc _ _ (hcommG 0 2 (Ne.symm hA20)))
        (hzc _ _ (hcommG 1 2 (Ne.symm hA21)))) (Subgroup.mem_zpowers _)) (hr'3 2)
  have hFbar : barM M F = Subgroup.zpowers (ρ 0) ⊔ Subgroup.zpowers (ρ 1) ⊔
      Subgroup.zpowers (ρ 2) := by
    rw [hF, barM_sup (sup_le ((Subgroup.zpowers_le).mpr (hRM (hrn 0)))
      ((Subgroup.zpowers_le).mpr (hRM (hrn 1)))) ((Subgroup.zpowers_le).mpr (hRM (hrn 2))),
      barM_sup ((Subgroup.zpowers_le).mpr (hRM (hrn 0))) ((Subgroup.zpowers_le).mpr (hRM (hrn 1))),
      barM_zpowers (hRM (hrn 0)), barM_zpowers (hRM (hrn 1)), barM_zpowers (hRM (hrn 2))]
  have hFcard : Nat.card F = 3 ^ 3 := by
    rw [← card_barM_of_isPGroup Nat.prime_three (by norm_num) (hFR.trans hRM) (hR3.to_le hFR),
      hFbar]
    exact hT.card_sup
  have hmemF : ∀ x ∈ R, (∀ f ∈ F, f * x = x * f) → x ^ 3 = 1 → x ∈ F := by
    intro x hx hxF hx3
    have hFx : F ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      intro f hf
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (show Commute x f from (hxF f hf).symm) n)).eq
    have hel := isElemAbelian_sup_zpowers_of_mem_centralizer hFel
      (Subgroup.le_centralizer_iff.mp hFx (Subgroup.mem_zpowers x)) hx3
    have hle := hrk _ (sup_le hFR ((Subgroup.zpowers_le).mpr hx)) hel
    have heq : F = F ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hFcard]; exact hle)
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hzF : z ∈ F := hmemF z hzR (fun f hf => (hRz f (hFR hf))) hz3
  have hwF : w ∈ F := hmemF w hwR (fun f hf => (hRw f (hFR hf))) hw3
  have hmbarF : ∀ x (hx : x ∈ F), mbar M x (hRM (hFR hx)) ∈ barM M F := fun x hx =>
    ⟨⟨x, hRM (hFR hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  set yb := mbar M y (hRM hy) with hyb
  have hstep : ∀ n, yb * ρ n * yb⁻¹ = ρ (n + 1) := fun n => by
    simp only [hρ, hyb]
    rw [← mbar_conj (hRM (hrn n)) (hRM hy)]
    congr 1
    group
  by_cases h30 : A 3 = A 0
  ·
    have h3 : ρ 3 = ρ 0 := by
      simp only [hρ]
      congr 1
      exact hrepeq 3 0 h30
    have hzeq : zb = ρ 0 * ρ 1 * ρ 2 := hT.eq_prod (hFbar ▸ hmbarF z hzF)
      (by rw [hρ0, hA0]; exact hrc) (hdat 1).2.2 (hdat 2).2.2
    have hwb := hT.mem_zpowers_prod (g := yb) (hFbar ▸ hmbarF w hwF) (hstep 0) (hstep 1)
      (by rw [hstep 2, h3]) (by
        rw [hyb, ← mbar_conj (hRM hwR) (hRM hy)]
        congr 1
        rw [hRw y hy, mul_inv_cancel_right])
    rw [← hzeq] at hwb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwb
    apply hwz
    have : w = z ^ n := eq_of_mbar_eq_p hp3 hp32 hRM hR3 hwR (R.zpow_mem hzR n) (by
      rw [mbar_zpow (hRM hzR) n, ← hzb, hn])
    rw [this]
    exact Subgroup.zpow_mem_zpowers z n
  ·
    have hc3 : ∀ m ∈ ({0, 1, 2} : Finset ℕ), r' m * r' 3 = r' 3 * r' m := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · exact hcommG 0 3 (Ne.symm h30)
      · exact hcommG 1 3 (Ne.symm hA31)
      · exact hcommG 2 3 (Ne.symm hA32)
    have hF3 : ∀ f ∈ F, f * r' 3 = r' 3 * f := by
      have hle : F ≤ Subgroup.centralizer ({r' 3} : Set G) := by
        refine sup_le (sup_le ?_ ?_) ?_ <;>
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact hc3 0 (by simp)
        · exact hc3 1 (by simp)
        · exact hc3 2 (by simp)
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
    have h3F : r' 3 ∈ F := hmemF _ (hrn 3) hF3 (hr'3 3)
    have hle : barM M F ≤ Subgroup.centralizer (A 3 : Set _) := by
      rw [hFbar]
      exact hT.sup_le_centralizer (hcen 0 3 (Ne.symm h30)) (hcen 1 3 (Ne.symm hA31))
        (hcen 2 3 (Ne.symm hA32))
    exact hρn 3 (hle (hmbarF _ h3F))

end CFSG.AGLEmbedding
