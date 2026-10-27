module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24HPerp
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23Setting.isUniqueInvolution_of_mem_perp (h : Hyp23Setting Ω K K' z)
    {L J : Subgroup G} (hL : L ∈ twinSet Ω K) (hJ : J ∈ KPerp Ω L) : IsUniqueInvolution J z := by
  rw [Q3T7P24.perp_of_twin3 h hL] at hJ
  rcases hJ with rfl | rfl
  · exact h.hz
  · exact isUniqueInvolution_of_mem_twinSet h.hz h.hK'

theorem Hyp23Setting.stdCent_of_twin (h : Hyp23Setting Ω K K' z) {H : Subgroup G}
    (hz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hz
  nonTwin := by
    intro L hL J hJ z' hz' hzz
    exfalso
    exact hzz (hz'.eq (h.isUniqueInvolution_of_mem_perp hL (Set.mem_insert_of_mem _ hJ)))
  twin := htwin
end Basic
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C23_2_trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 →
      u ≠ z → u * u = 1 → ∀ J ∈ dstarComp Ω K,
        ∃ h ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G),
          conjSub h K = J

@[expose] def C23_2_fuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 →
      u ≠ z → u * u = 1 → ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
        IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
          orderOf x = 4 → orderOf y = 4 →
            ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * u * c⁻¹ = x * y
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement MatrixGroups

theorem c23_2_fuse : C23_2_fuse := by
  intro G _ _ _ Ω K K' z hs _ _ _ u hu _ hu1 huz hu2 L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy
    ox oy
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hLΩ : L ∈ Ω := hL.1
  have hL'Ω : L' ∈ Ω := hL'.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hs.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet hs.hz hL'

  have hM : K ⊔ K' = L ⊔ L' := by
    have hLm : L ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL
    have hL'm : L' ∈ ({K, K'} : Set (Subgroup G)) := hs.twinSet_eq ▸ hL'
    rcases hLm with rfl | rfl <;> rcases hL'm with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact sup_comm _ _
    · exact absurd rfl hne
  have huM : u ∈ L ⊔ L' := hM ▸ hu
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    hΩ.le_normalizer_of_twin hLΩ hL'Ω hne.symm hzL hzL'
  have hLC : L ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hLC hL'C

  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    T7A.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr huM)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  have hu'2 : (a * b) * (a * b) = 1 := by
    rw [hab]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu'2
  have haL : a ∈ L := hR₁.1 ha
  have hbL' : b ∈ L' := hR₂.1 hb
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hLΩ hL'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzL.unique (a * a) (L.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzL.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzL'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = z := by
        rw [← hab]
        rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
        · left; rw [h1, h2, one_mul]
        · right; rw [h1, h2, one_mul]
        · right; rw [h1, h2, mul_one]
        · left; rw [h1, h2]; exact hzL.sq
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rcases hu'z with h' | h'
      · exact hu1 (by rw [hu, h']; group)
      · exact huz (by
          rw [hu, h']
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group)
    · exact h
  have hbb : b * b = z := by
    have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzL.sq
  have hx2 : x * x = z := T7B.mul_self_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hy2 : y * y = z := T7B.mul_self_eq_of_orderOf_four hzL' (hR₂.1 hy) oy

  obtain ⟨k, hkL, hk⟩ := T7B.exists_conj_of_sq_eq hΩ hLΩ hzL haL (hR₁.1 hx) haa hx2
  set b₁ := k * b * k⁻¹ with hb₁
  have hb₁L' : b₁ ∈ L' := (Subgroup.mem_normalizer_iff.mp (hLN hkL) b).mp hbL'
  have hb₁2 : b₁ * b₁ = z := by
    have e : b₁ * b₁ = k * (b * b) * k⁻¹ := by rw [hb₁]; group
    rw [e, hbb]
    have := hzL.commute_of_mem hkL
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  have hxb₁ : x * b₁ = b₁ * x := by
    rw [← hk, hb₁]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hcab]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  have hxy : x * y = y * x := hc x hx y hy

  obtain ⟨ℓ, hℓL', hℓ⟩ := T7B.exists_conj_of_sq_eq hΩ hL'Ω hzL' hb₁L' (hR₂.1 hy) hb₁2 hy2

  obtain ⟨ℓ', hℓ'L', hℓ'b, hℓ'x⟩ := T7B.exists_centralizing_conj hΩ hLΩ hL'Ω hne hzL hzL'
    (hR₁.1 hx) (T7B.isPGroup_zpowers_of_orderOf_four ox) hℓL' hxb₁ hxy hℓ

  refine ⟨ℓ' * k * m, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL'C hℓ'L') (hLC hkL))
    (hMC hmM), ?_⟩
  have hℓ'x' : ℓ' * x * ℓ'⁻¹ = x := by
    rw [hℓ'x]
    group
  calc ℓ' * k * m * u * (ℓ' * k * m)⁻¹ = ℓ' * k * (m * u * m⁻¹) * k⁻¹ * ℓ'⁻¹ := by group
    _ = ℓ' * k * (a * b) * k⁻¹ * ℓ'⁻¹ := by rw [hab]
    _ = ℓ' * ((k * a * k⁻¹) * (k * b * k⁻¹)) * ℓ'⁻¹ := by group
    _ = ℓ' * (x * b₁) * ℓ'⁻¹ := by rw [hk]
    _ = (ℓ' * x * ℓ'⁻¹) * (ℓ' * b₁ * ℓ'⁻¹) := by group
    _ = x * y := by rw [hℓ'x', hℓ'b]
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem rep_R_le (c : Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {H : Subgroup G}
    (hr : F.ρ.r ∈ H) (hr' : F.ρ'.r ∈ H) (hs : F.ρ₃.r ∈ H) (hWH : W ⊔ OCW W ≤ H)
    (σ : Thompson.Rep Ω W) : σ.R ≤ H := by
  have hmem : ∀ w : G, w ∈ H → w ∈ Subgroup.normalizer (W : Set G) →
      Thompson.piG W σ.r = Thompson.piG W w → σ.r ∈ H := by
    intro w hwH hwN hpi
    have h1 := (Thompson.piG_eq_iff hwN σ.r_mem_normalizer).mp hpi.symm
    have h2 : w⁻¹ * σ.r ∈ H := hWH h1
    have h3 : σ.r = w * (w⁻¹ * σ.r) := by group
    rw [h3]
    exact H.mul_mem hwH h2
  have hrN := F.ρ.r_mem_normalizer
  have hr'N := F.ρ'.r_mem_normalizer
  have hsN := F.ρ₃.r_mem_normalizer
  have hσ : σ.r ∈ H := by
    rcases swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃) hab
      hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
    · exact hmem F.ρ.r hr hrN (congrArg Subtype.val h)
    · exact hmem F.ρ'.r hr' hr'N (congrArg Subtype.val h)
    · exact hmem F.ρ₃.r hs hsN (congrArg Subtype.val h)
    · refine hmem (F.ρ.r * F.ρ₃.r * F.ρ.r) (H.mul_mem (H.mul_mem hr hs) hr)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hsN) hrN) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ hrN hsN) hrN, Thompson.piG_mul hrN hsN]
      exact congrArg Subtype.val h
    · refine hmem (F.ρ'.r * F.ρ₃.r * F.ρ'.r) (H.mul_mem (H.mul_mem hr' hs) hr')
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr'N hsN) hr'N) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ hr'N hsN) hr'N, Thompson.piG_mul hr'N hsN]
      exact congrArg Subtype.val h
    · refine hmem (F.ρ.r * F.ρ'.r * F.ρ₃.r * F.ρ'.r * F.ρ.r)
        (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hr hr') hs) hr') hr)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.mul_mem _ hrN hr'N) hsN) hr'N) hrN) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hr'N)
        hsN) hr'N) hrN, Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hr'N) hsN)
        hr'N, Thompson.piG_mul (Subgroup.mul_mem _ hrN hr'N) hsN, Thompson.piG_mul hrN hr'N]
      exact congrArg Subtype.val h
  intro x hx
  by_cases hxW : x ∈ W
  · exact hWH (Subgroup.mem_sup_left hxW)
  · have h1 : σ.r⁻¹ * x ∈ W :=
      Q3CL.Thompson.D_inv_mul_mem c.hΩ c.hW σ.hR σ.hr hx σ.hrW hxW
    have h2 : x = σ.r * (σ.r⁻¹ * x) := by group
    rw [h2]
    exact H.mul_mem hσ (hWH (Subgroup.mem_sup_left h1))
end T7E

theorem c23_2_trans_proved : C23_2_trans := by
  intro G _ _ _ Ω K K' z hs W hW hzW u huK huW hu1 huz hu2 J hJ
  have hst : AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaModT Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  set H := Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) with hH
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ H := le_sup_left
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := le_sup_right
  have hKH : ∀ k ∈ K, k ∈ H := fun k hk =>
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hk).symm)
  have hK'H : ∀ k ∈ K', k ∈ H := fun k hk =>
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hk).symm)

  obtain ⟨g₀, hg₀⟩ := hst.trans K' hK'
  have hg₀z : g₀ * z * g₀⁻¹ = z := by
    have := hz.conj g₀
    rw [hg₀] at this
    exact (hz'.eq this).symm
  have hg₀H : g₀ ∈ H :=
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg₀z))

  have key : ∀ W₁ : Subgroup G, W₁ ∈ WSet Ω → z ∈ W₁ → ∀ J' : Subgroup G, J' ∈ Ω →
      (∃ T ∈ DSet Ω W₁, IsSylow2In T J') → ∃ h ∈ H, conjSub h K = J' := by
    intro W₁ hW₁ hzW₁ J' hJ' ⟨T, hTD, hTJ'⟩
    have c : Q3CL.Thompson.Ctx Ω W₁ := T7D.ctx_of_stand hst hW₁
    obtain ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρS, hρ'S, hnbr, hnbr', hab, hcomm⟩ :=
      T7E.exists_twin_reps hs hW₁ hzW₁
    obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hΩ hW₁ hJ' hTJ' hTD
    rcases T7E.rep_dichotomy hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
    · rcases hall σ with h | h
      · exact ⟨1, H.one_mem, by rw [conjSub_one, ← hσK, h, hρK]⟩
      · exact ⟨g₀, hg₀H, by rw [hg₀, ← hσK, h, hρ'K]⟩
    · obtain ⟨F, hFρ, hFρ', hFρ₃, hFz⟩ :=
        T7E.frame4_of_twin_reps hs hW₁ hρK hρ'K hnbr hnbr' hac hbc
      subst hFρ hFρ' hFρ₃
      obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, -⟩ :=
        F.exists_structure c he hab hcomm hac
      have mx₁ : x₁ ∈ F.ρ.R ⊓ W₁ := h₁ ▸ Subgroup.mem_zpowers x₁
      have mx₂ : x₂ ∈ F.ρ'.R ⊓ W₁ := h₂ ▸ Subgroup.mem_zpowers x₂
      have hbR : x₁ ^ m ∈ F.ρ.R := F.ρ.R.pow_mem mx₁.1 m
      have hb'R : x₂ ^ m ∈ F.ρ'.R := F.ρ'.R.pow_mem mx₂.1 m
      have ob : orderOf (x₁ ^ m) = 4 := by
        have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega)
          (by rw [o₁]; exact dvd_mul_left m 4)
        rwa [o₁, Nat.mul_div_cancel _ hm] at this
      have ob' : orderOf (x₂ ^ m) = 4 := by
        have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega)
          (by rw [o₂]; exact dvd_mul_left m 4)
        rwa [o₂, Nat.mul_div_cancel _ hm] at this
      have hbK : x₁ ^ m ∈ F.ρ.K ⊓ W₁ := ⟨F.ρ.hRK.1 hbR, W₁.pow_mem mx₁.2 m⟩
      have hb'K : x₂ ^ m ∈ F.ρ'.K ⊓ W₁ := ⟨F.ρ'.hRK.1 hb'R, W₁.pow_mem mx₂.2 m⟩
      obtain ⟨u₁, hu₁, hsu, -⟩ := T7D.frame_fixed c F.ρ F.ρ' F.ρ₃ F.hnbr F.hnbr' F.hne₁ F.hne₂
        F.hn₁ F.hn₂ F.hn₁' F.hn₂' F.hz F.hz' F.hj hbK hb'K ob ob'
      have hRsyl : IsSylow2In F.ρ.R K := by rw [← hρK]; exact F.ρ.hRK
      have hR'syl : IsSylow2In F.ρ'.R K' := by rw [← hρ'K]; exact F.ρ'.hRK
      have hc2 : Commutes F.ρ.R F.ρ'.R :=
        hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' (hρK ▸ F.ρ.hRK.1)
          (hρ'K ▸ F.ρ'.hRK.1) (S.isPGroup'.to_le (sup_le hρS hρ'S))
      have hCx : ∀ x ∈ F.ρ.R, ∀ y ∈ F.ρ'.R, orderOf x = 4 → orderOf y = 4 →
          Subgroup.centralizer ({x * y} : Set G) ≤ H := by
        intro x hx y hy ox oy t ht
        obtain ⟨c₁, hc₁, hc₁u⟩ := c23_2_fuse G Ω K K' z hs W hW hzW u huK huW
          hu1 huz hu2 K (mem_twinSet_self hK hz) K' hs.hK' hKK' F.ρ.R F.ρ'.R hRsyl hR'syl hc2
          x hx y hy ox oy
        have ht' : t * (x * y) = (x * y) * t := Subgroup.mem_centralizer_singleton_iff.mp ht
        have hu' : u = c₁⁻¹ * (x * y) * c₁ := by rw [← hc₁u]; group
        have hmem : c₁⁻¹ * t * c₁ ∈ Subgroup.centralizer ({u} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc c₁⁻¹ * t * c₁ * u = c₁⁻¹ * (t * (x * y)) * c₁ := by rw [hu']; group
            _ = c₁⁻¹ * ((x * y) * t) * c₁ := by rw [ht']
            _ = u * (c₁⁻¹ * t * c₁) := by rw [hu']; group
        have h4 : t = c₁ * (c₁⁻¹ * t * c₁) * c₁⁻¹ := by group
        rw [h4]
        exact H.mul_mem (H.mul_mem (hCz hc₁) (hCu hmem)) (H.inv_mem (hCz hc₁))
      have hu₁H : Subgroup.centralizer ({u₁} : Set G) ≤ H := by
        rcases hu₁ with rfl | rfl
        · exact hCx _ hbR _ hb'R ob ob'
        · exact hCx _ (F.ρ.R.inv_mem hbR) _ hb'R (by rw [orderOf_inv]; exact ob) ob'
      have hu₁W : u₁ ∈ W₁ := by
        rcases hu₁ with rfl | rfl
        · exact W₁.mul_mem (W₁.pow_mem mx₁.2 m) (W₁.pow_mem mx₂.2 m)
        · exact W₁.mul_mem (W₁.inv_mem (W₁.pow_mem mx₁.2 m)) (W₁.pow_mem mx₂.2 m)
      have hsH : F.ρ₃.r ∈ H := hu₁H (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hsu))
      have hWH : W₁ ⊔ OCW W₁ ≤ H := by
        refine sup_le (fun w hw => hu₁H ?_) (fun w hw => hu₁H ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw u₁ hu₁W)
        · have := Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W₁ hw) u₁ hu₁W
          exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
      have hrH : F.ρ.r ∈ H := hKH _ (by rw [← hρK]; exact F.ρ.hRK.1 F.ρ.hr)
      have hr'H : F.ρ'.r ∈ H := hK'H _ (by rw [← hρ'K]; exact F.ρ'.hRK.1 F.ρ'.hr)
      have hDH := T7E.rep_R_le c F he hab hcomm hac hrH hr'H hsH hWH
      have hMH : MGrp Ω W₁ ≤ H := iSup₂_le fun R hR => by
        obtain ⟨KR, hKR, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
        obtain ⟨σ', -, hσ'R⟩ := T7D.exists_rep hΩ hW₁ hKR hRK hR
        rw [← hσ'R]
        exact hDH σ'
      obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
      obtain ⟨m', hm'M, hym'⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
      have hm'N : m' ∈ Subgroup.normalizer (W₁ : Set G) := Thompson.MGrp_le_normalizer Ω W₁ hm'M
      have himg : Thompson.piG W₁ m' * F.ρ.img * (Thompson.piG W₁ m')⁻¹ = σ.img := by
        rw [← hym']
        exact congrArg Subtype.val hy
      have hKm : conjSub m' F.ρ.K = σ.K :=
        c.K_eq_of_img_eq (T7D.conjRep c.hΩ hm'N F.ρ) σ (by rw [T7D.conjRep_img, himg])
      exact ⟨m', hMH hm'M, by rw [← hσK, ← hKm, hρK]⟩

  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' → ∃ h ∈ H, conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h
      have hzW₁ : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩

  have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h | h⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
