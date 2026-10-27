module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenData
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFamMain

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_convI_mem_autI_gen {X K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hKX : K ≤ X)
    (hC : X ⊓ Subgroup.centralizer (V : Set G) ≤ K) {x : G} (hx : x ∈ X)
    (hxK : convI hV ⟨x, hXN hx⟩ ∈ autI hV K) : x ∈ K := by
  obtain ⟨k, hkK, hk⟩ := (mem_autI hV).1 hxK
  have h1 : convI hV (⟨x, hXN hx⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hk, mul_inv_cancel]
  have h2 : x * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
  have h3 : x * (k : G)⁻¹ ∈ X := X.mul_mem hx (X.inv_mem (hKX hkK))
  have h4 : x * (k : G)⁻¹ ∈ K := hC ⟨h3, h2⟩
  have : x = (x * (k : G)⁻¹) * k := by group
  rw [this]
  exact K.mul_mem h4 hkK

theorem normalizer_le_normalizer_twoResidual_gen (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (twoResidual X : Set G) := by
  intro g hg
  have hgX : ∀ x, x ∈ X ↔ g * x * g⁻¹ ∈ X := Subgroup.mem_normalizer_iff.1 hg
  set K' : Subgroup G := X ⊓ (twoResidual X).comap (MulAut.conj g).toMonoidHom with hK'
  have hmemK' : ∀ x, x ∈ K' ↔ x ∈ X ∧ g * x * g⁻¹ ∈ twoResidual X := fun x => by
    simp [hK']
  have hN : X ≤ Subgroup.normalizer (K' : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' := (hmemK' n).1 hn
    refine (hmemK' _).2 ⟨X.mul_mem (X.mul_mem hx hn'.1) (X.inv_mem hx), ?_⟩
    have hxg : g * x * g⁻¹ ∈ X := (hgX x).1 hx
    have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual X hxg)
      (g * n * g⁻¹)).1 hn'.2
    have e : g * (x * n * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * n * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact h2
  have h2q : ∀ y ∈ X, ∃ k : ℕ, y ^ 2 ^ k ∈ K' := by
    intro y hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X (g * y * g⁻¹) ((hgX y).1 hy)
    refine ⟨k, (hmemK' _).2 ⟨X.pow_mem hy _, ?_⟩⟩
    rw [conj_pow.symm]
    exact hk
  have hle : twoResidual X ≤ K' := twoResidual_le_of_isTwoQuotient inf_le_left hN h2q
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  exact ((hmemK' n).1 (hle hn)).2

theorem exists_genSetting_data {H T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V) (hVZ : V = VZ T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    (hS : SymCaseGen H T V hV) :
    ∃ (N : ℕ) (Y : Subgroup G), GenSetting H T M V Y hV ∧ Nonempty (GenData N H T V Y hV) := by
  obtain ⟨m, -, ⟨F⟩⟩ := exists_genFamData hV hmin hred hJ hS
  have hKJ : twoResidual H ≤ thompsonJ H := hS.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hT := hmin.isSylow
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (hT.1.trans hle))
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
    MinParabolic.pCoreOf_le_centralizer hred
  set Pc : Subgroup G := preI hV H hHN F.C with hPc
  set Y₀ : Subgroup G := twoResidual H ⊓ Pc with hY₀
  set Y : Subgroup G := twoResidual Y₀ with hY
  have hYY₀ : Y ≤ Y₀ := twoResidual_le Y₀
  have hYK : Y ≤ twoResidual H := hYY₀.trans inf_le_left
  have hYH : Y ≤ H := hYK.trans (twoResidual_le H)
  have hoddC : ∀ φ ∈ F.C, Odd (orderOf φ) := by
    intro φ hφ
    have hd : orderOf φ ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard F.C hφ
      rwa [F.C_card] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
  have hY₀C : autI hV Y₀ ≤ F.C := by
    intro φ hφ
    obtain ⟨g, hgY, rfl⟩ := (mem_autI hV).1 hφ
    exact ((mem_preI hV).1 (Subgroup.mem_inf.1 hgY).2).2
  have hCY₀ : F.C ≤ autI hV Y₀ := by
    intro φ hφ
    have hφH : φ ∈ autI hV H := autI_mono hV (thompsonJ_le_self H) (F.L_J (F.C_le hφ))
    obtain ⟨g, hgK, hgφ⟩ := (mem_autI hV).1
      (E2.mem_autI_twoResidual_of_odd (hV := hV) hφH (hoddC φ hφ))
    refine (mem_autI hV).2 ⟨g, Subgroup.mem_inf.2 ⟨hgK, (mem_preI hV).2
      ⟨twoResidual_le H hgK, ?_⟩⟩, hgφ⟩
    have e : convHom hV H hHN ⟨(g : G), twoResidual_le H hgK⟩ = φ := hgφ
    rw [e]
    exact hφ
  have hYC : autI hV Y = F.C := by
    refine le_antisymm ((autI_mono hV hYY₀).trans hY₀C) fun φ hφ => ?_
    obtain ⟨g, hgY, rfl⟩ := (mem_autI hV).1 (hCY₀ hφ)
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient Y₀ (g : G) hgY
    refine mem_of_odd_orderOf_of_pow_mem (hoddC _ hφ) (k := k) ?_
    exact (mem_autI hV).2 ⟨g ^ 2 ^ k, by simpa using hk, map_pow _ _ _⟩
  have hnormY : ∀ g : ↥H, convHom hV H hHN g ∈
      Subgroup.normalizer (F.C : Set (MulAut (IntMod V hV))) →
      (g : G) ∈ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    have hY₀N : (g : G) ∈ Subgroup.normalizer (Y₀ : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨hnK, hnPc⟩ := Subgroup.mem_inf.1 hn
      obtain ⟨hnH, hnC⟩ := (mem_preI hV).1 hnPc
      have hgn : (g : G) * n * (g : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem g.2 hnH) (H.inv_mem g.2)
      refine Subgroup.mem_inf.2 ⟨?_, (mem_preI hV).2 ⟨hgn, ?_⟩⟩
      · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual H g.2) n).1 hnK
      · show convHom hV H hHN (g * ⟨n, hnH⟩ * g⁻¹) ∈ F.C
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 hg _).1 hnC
    exact normalizer_le_normalizer_twoResidual_gen Y₀ hY₀N
  have hQnorm : pCoreOf 2 H ≤ Subgroup.normalizer (Y : Set G) := by
    intro q hq
    have hqH : q ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hq
    have h1 : convHom hV H hHN ⟨q, hqH⟩ = 1 := (convI_eq_one_iff hV ⟨q, hHN hqH⟩).2 (hQC hq)
    exact hnormY ⟨q, hqH⟩ (by rw [h1]; exact one_mem _)
  have hSnorm : baum T ≤ Subgroup.normalizer (Y : Set G) := by
    intro s hs
    have hsH : s ∈ H := hT.1 hs.1
    exact hnormY ⟨s, hsH⟩ (F.baum_C (convI_mem_autI hV hs (hHN hsH)))
  have hgen : Y ⊔ T = H := by
    refine hmin.eq_of_not_le le_sup_right (sup_le hYH hT.1) fun hM => ?_
    have hCM : F.C ≤ autI hV M := by
      rw [← hYC]
      exact autI_mono hV (le_sup_left.trans hM)
    have hTM : autI hV T ≤ autI hV M := autI_mono hV hmin.le
    have hJM := F.gen_J _ hTM (F.gen_L _ hTM hCM)
    have hC : H ⊓ Subgroup.centralizer (V : Set G) ≤ M :=
      (hmin.inf_centralizer_le_kerIn hred hHV).trans kerIn_le
    have hKM : twoResidual H ≤ M := fun x hx =>
      mem_of_convI_mem_autI_gen hV hHN hmin.maximal.1.le hC (twoResidual_le H hx)
        (hJM (convI_mem_autI hV (hKJ hx) (hHN (twoResidual_le H hx))))
    have hHM : H ≤ M := by
      rw [← sup_twoResidual_eq hT]
      exact sup_le hmin.le hKM
    exact absurd (lt_of_le_of_lt hHM hmin.maximal.1) (lt_irrefl _)
  refine ⟨2 ^ m + 1, Y, ⟨hmin, hF, hred, hJ, hVZ, hYH, twoResidual_twoResidual Y₀,
    fun x hx => hRad ⟨hYK hx.1, hx.2⟩, by rw [hYC]; exact F.C_card, hQnorm, hSnorm, hgen⟩,
    ⟨⟨F.hN, F.hodd, F.L, F.θ, F.β, F.hβ, F.a, F.b, F.p, F.hab, F.hbp, F.hap,
      F.L_J.trans (autI_mono hV (thompsonJ_le_self H)), F.L_J, F.J_N,
      fun φ hφ => F.C_θ φ (hYC.le hφ), F.t_lift⟩⟩⟩

end CFSG.AGLEmbeddingD2.GN
