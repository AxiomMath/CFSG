module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LK
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts.TG3 (injOn_of_natCard_map3 natCard_sl2_three)
open scoped MatrixGroups commutatorElement

@[expose] def FrameAt {X : Type} [Group X] (Φ : Set (Subgroup X)) (zb a : X) : Prop :=
  ∃ M ∈ Φ, ∃ b u : X, IsUniqueInvolution M b ∧ b ≠ a ∧ b ≠ zb * a ∧ a * b = b * a ∧
    u ∈ M ∧ orderOf u = 4 ∧ u * u = b ∧ a * u = u * a ∧
    (∃ C ∈ Φ, IsUniqueInvolution C (a * b)) ∧
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) ⊔
      Subgroup.centralizer ({a * b} : Set X) = ⊤

@[expose] def PairAt {X : Type} [Group X] (Φ : Set (Subgroup X)) (zb : X) : Prop :=
  zb ≠ 1 ∧ ∃ A ∈ Φ, ∃ A' ∈ Φ, ∃ a a' : X, IsUniqueInvolution A a ∧ IsUniqueInvolution A' a' ∧
    (∀ x ∈ A, ∀ y ∈ A', x * y = y * x) ∧ zb = a * a'

section Group

variable {K X : Type} [Group K] [Group X]

theorem isUniqueInvolution_map_of_inj (ψ : K →* X) {R : Subgroup K}
    (hinj : ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s) {r : K} (h : IsUniqueInvolution R r) :
    IsUniqueInvolution (R.map ψ) (ψ r) where
  mem := Subgroup.mem_map_of_mem ψ h.mem
  ne_one := fun h1 => h.ne_one (hinj _ h.mem 1 R.one_mem (h1.trans (map_one ψ).symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨s, hs, rfl⟩ hy
    have hss : s * s = 1 :=
      hinj _ (R.mul_mem hs hs) 1 R.one_mem (by rw [map_mul, hy, map_one])
    rcases h.unique s hs hss with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])

theorem map_centralizer_le (ψ : K →* X) (a : K) :
    (Subgroup.centralizer ({a} : Set K)).map ψ ≤ Subgroup.centralizer ({ψ a} : Set X) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy']

theorem sup_centralizer_eq_top_of_map (ψ : K →* X) (hψ : Function.Surjective ψ) {a b c : K}
    (h : Subgroup.centralizer ({a} : Set K) ⊔ Subgroup.centralizer ({b} : Set K) ⊔
      Subgroup.centralizer ({c} : Set K) = ⊤) :
    Subgroup.centralizer ({ψ a} : Set X) ⊔ Subgroup.centralizer ({ψ b} : Set X) ⊔
      Subgroup.centralizer ({ψ c} : Set X) = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : Subgroup X) = (⊤ : Subgroup K).map ψ := (Subgroup.map_top_of_surjective ψ hψ).symm
  rw [h1, ← h, Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le_sup (sup_le_sup (map_centralizer_le ψ a) (map_centralizer_le ψ b))
    (map_centralizer_le ψ c)

theorem mem_center_of_map_central (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) {g : K}
    (hg : ψ g ∈ Subgroup.center X) : g ∈ Subgroup.center K := by
  have hcen : ∀ y : K, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.center K := fun y => by
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have := Subgroup.mem_center_iff.mp hg (ψ y)
    calc ψ g * ψ y * (ψ g)⁻¹ * (ψ y)⁻¹ = (ψ g * ψ y) * (ψ g)⁻¹ * (ψ y)⁻¹ := rfl
      _ = (ψ y * ψ g) * (ψ g)⁻¹ * (ψ y)⁻¹ := by rw [this]
      _ = 1 := by group
  let φ : K →* K :=
    { toFun := fun y => g * y * g⁻¹ * y⁻¹
      map_one' := by simp
      map_mul' := fun y z => by
        have hz := Subgroup.mem_center_iff.mp (hcen z) y
        calc g * (y * z) * g⁻¹ * (y * z)⁻¹ =
            (g * y * g⁻¹ * y⁻¹) * (y * (g * z * g⁻¹ * z⁻¹) * y⁻¹) := by group
          _ = (g * y * g⁻¹ * y⁻¹) * (g * z * g⁻¹ * z⁻¹) := by
            rw [hz]; group }
  have hφ : ∀ y z : K, φ ⁅y, z⁆ = 1 := fun y z => by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hcen z) (φ y))
  have hle : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ φ.ker :=
    Subgroup.commutator_le.mpr fun y _ z _ => hφ y z
  rw [hperf] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have : g * y * g⁻¹ * y⁻¹ = 1 := hle (Subgroup.mem_top y)
  calc y * g = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y) * 1 * 1 := by group
    _ = g * y := by rw [this]; group

end Group

section Cover

local notation "𝔽₃" => GaloisField 3 1

variable {K X : Type} [Group K] [Group X] {V : Type} [AddCommGroup V] [Module 𝔽₃ V]
  [FiniteDimensional 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem injOn_member [Finite K] (ψ : K →* X) {R : Subgroup K} (e : R ≃* SL(2, 𝔽₃))
    (h24 : Nat.card (R.map ψ) = 24) : ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := by
  have hRcard : Nat.card R = Nat.card (R.map ψ) := by
    rw [h24, Nat.card_congr e.toEquiv]
    exact natCard_sl2_three
  exact injOn_of_natCard_map3 ψ hRcard

theorem member_map_mem (ψ : K →* X) {𝓕 : Set (Subgroup K)} {Φ : Set (Subgroup X)}
    (hΦ : ConjInvariant Φ) (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : K, R' = conjSub g R)
    (hmeets : ∃ R ∈ 𝓕, R.map ψ ∈ Φ) {R : Subgroup K} (hR : R ∈ 𝓕) : R.map ψ ∈ Φ := by
  obtain ⟨R₀, hR₀, hΦ₀⟩ := hmeets
  obtain ⟨g, hg⟩ := hsingle R₀ hR₀ R hR
  rw [hg, map_conjSub]
  exact hΦ (ψ g) _ hΦ₀

theorem trans_of_cover (ψ : K →* X) {𝓕 : Set (Subgroup K)} {Φ : Set (Subgroup X)}
    (hΦF : ∀ L ∈ Φ, ∃ R ∈ 𝓕, L = R.map ψ)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : K, R' = conjSub g R) :
    ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B := by
  intro A hA B hB
  obtain ⟨R, hR, rfl⟩ := hΦF A hA
  obtain ⟨R', hR', rfl⟩ := hΦF B hB
  obtain ⟨g, hg⟩ := hsingle R hR R' hR'
  exact ⟨ψ g, by rw [hg, map_conjSub]⟩

theorem claimZ {Φ : Set (Subgroup X)} {zb : X} (hΦ : ConjInvariant Φ)
    (hzbc : zb ∈ Subgroup.center X)
    (htrans : ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B) (hP : PairAt Φ zb)
    {M : Subgroup X} (hM : M ∈ Φ) {m : X} (hm : IsUniqueInvolution M m) :
    ∃ M' ∈ Φ, IsUniqueInvolution M' (zb * m) := by
  obtain ⟨-, A, hA, A', hA', a, a', hUa, hUa', -, hzb⟩ := hP
  obtain ⟨g, hg⟩ := htrans A hA M hM
  have h1 : IsUniqueInvolution M (g * a * g⁻¹) := hg ▸ hUa.conj g
  have hma : m = g * a * g⁻¹ := hm.eq h1
  refine ⟨conjSub g A', hΦ g A' hA', ?_⟩
  have h2 := hUa'.conj g
  have ha' : a' = a * zb := by
    calc a' = a⁻¹ * (a * a') := by group
      _ = a⁻¹ * zb := by rw [← hzb]
      _ = a * zb := by rw [inv_eq_of_mul_eq_one_right hUa.sq]
  have hz : g * zb * g⁻¹ = zb := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.mp hzbc g
  have : g * a' * g⁻¹ = zb * m := by
    rw [ha', hma]
    calc g * (a * zb) * g⁻¹ = (g * a * g⁻¹) * (g * zb * g⁻¹) := by group
      _ = (g * a * g⁻¹) * zb := by rw [hz]
      _ = zb * (g * a * g⁻¹) := (Subgroup.mem_center_iff.mp hzbc _)
  rw [this] at h2
  exact h2

theorem psi_z₀_eq [Finite K] (ψ : K →* X) (hψk : ψ.ker ≤ Subgroup.center K)
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    {θ : K →* (V ≃ₗ[𝔽₃] V)} {𝓕 : Set (Subgroup K)} {z₀ : K} (D : CoverData Q θ 𝓕 z₀)
    (hopp : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False)
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃))) {Φ : Set (Subgroup X)} {zb : X}
    (hzbc : zb ∈ Subgroup.center X) (hΦF : ∀ L ∈ Φ, ∃ R ∈ 𝓕, L = R.map ψ)
    (hcard : ∀ L ∈ Φ, Nat.card L = 24) (hP : PairAt Φ zb) : ψ z₀ = zb := by
  have hodd := CFSG.ClassicalInvolution.ModelFacts.TG3.odd_natCard_galoisField_three
  obtain ⟨hzb1, A, hA, A', hA', a, a', hUa, hUa', -, hzb⟩ := hP
  obtain ⟨R, hR, rfl⟩ := hΦF A hA
  obtain ⟨R', hR', rfl⟩ := hΦF A' hA'
  have hinj := injOn_member ψ (hsl2 R hR).some (hcard _ hA)
  have hinj' := injOn_member ψ (hsl2 R' hR').some (hcard _ hA')
  obtain ⟨Fr, hFr⟩ := D.map_mem R hR
  obtain ⟨Fr', hFr'⟩ := D.map_mem R' hR'
  obtain ⟨r, hUr, hθr⟩ := exists_involution hodd D hR hFr
  obtain ⟨r', hUr', hθr'⟩ := exists_involution hodd D hR' hFr'
  have hψr : ψ r = a := (isUniqueInvolution_map_of_inj ψ hinj hUr).eq hUa
  have hψr' : ψ r' = a' := (isUniqueInvolution_map_of_inj ψ hinj' hUr').eq hUa'
  have hψg : ψ (r * r') = zb := by rw [map_mul, hψr, hψr', ← hzb]
  have hgc : r * r' ∈ Subgroup.center K :=
    mem_center_of_map_central ψ hψk hperf (by rw [hψg]; exact hzbc)
  have hcomm : r * r' = r' * r := by
    have h1 := Subgroup.mem_center_iff.mp hgc r
    exact mul_left_cancel (a := r) (by simpa [mul_assoc] using h1)
  have hgg : (r * r') * (r * r') = 1 := by
    calc (r * r') * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [← hcomm]
      _ = (r * r) * (r' * r') := by group
      _ = 1 := by rw [hUr.sq, hUr'.sq, one_mul]
  obtain ⟨c, hc⟩ := mem_scalars.mp (D.center_le _ hgc)
  have hθgg : θ (r * r') * θ (r * r') = 1 := by rw [← map_mul, hgg, map_one]
  have hcc : c * c = 1 := by
    have h1 := LinearEquiv.congr_fun hθgg Fr.P.e
    rw [LinearEquiv.mul_apply, hc, hc, smul_smul] at h1
    have h2 : (c * c) • Fr.P.e = (1 : 𝔽₃) • Fr.P.e := by rw [one_smul]; exact h1
    exact smul_left_injective 𝔽₃ Fr.P.e_ne_zero h2
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · have hk : r * r' ∈ θ.ker := by
      rw [MonoidHom.mem_ker]
      refine LinearEquiv.ext fun v => ?_
      rw [hc, h1, one_smul]
      rfl
    rcases D.ker_two _ hk with h | h
    · exact absurd (by rw [← hψg, h, map_one]) hzb1
    · rw [← h]; exact hψg
  · exfalso
    have e1 : ∀ v, Fr.La (-1) (Fr'.La (-1) v) = (-1 : 𝔽₃) • v := fun v => by
      have := hc v
      rwa [map_mul, hθr, hθr', h1, LinearEquiv.mul_apply] at this
    have e2 : ∀ w, Fr.La (-1) (Fr.La (-1) w) = w := fun w =>
      LinearEquiv.congr_fun (Frame.La_neg_one_mul_self Fr) w
    refine hopp Fr Fr' (LinearEquiv.ext fun v => ?_)
    show Fr'.La (-1) v = -(Fr.La (-1) v)
    calc Fr'.La (-1) v = Fr.La (-1) (Fr.La (-1) (Fr'.La (-1) v)) := (e2 _).symm
      _ = Fr.La (-1) ((-1 : 𝔽₃) • v) := by rw [e1]
      _ = -(Fr.La (-1) v) := by rw [map_smul, neg_one_smul]

theorem exists_frameAt_of_cover [Finite K] (ψ : K →* X) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker ≤ Subgroup.center K) (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    {θ : K →* (V ≃ₗ[𝔽₃] V)} {𝓕 : Set (Subgroup K)} {z₀ : K} (D : CoverData Q θ 𝓕 z₀)
    (hV : VFrames Q)
    (hopp : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False)
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : K, R' = conjSub g R) {Φ : Set (Subgroup X)} {zb : X}
    (hΦ : ConjInvariant Φ) (hΦF : ∀ L ∈ Φ, ∃ R ∈ 𝓕, L = R.map ψ)
    (hmeets : ∃ R ∈ 𝓕, R.map ψ ∈ Φ) (hcard : ∀ L ∈ Φ, Nat.card L = 24)
    (hzb : ∃ f ∈ Subgroup.center K, ψ f = zb) (hP : PairAt Φ zb) :
    ∃ A₀ ∈ Φ, ∃ a₀ : X, IsUniqueInvolution A₀ a₀ ∧ FrameAt Φ zb a₀ := by
  have hodd := CFSG.ClassicalInvolution.ModelFacts.TG3.odd_natCard_galoisField_three
  have hzbc : zb ∈ Subgroup.center X := by
    obtain ⟨f, hf, rfl⟩ := hzb
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k, rfl⟩ := hψs x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hf k]
  have hz₀ : ψ z₀ = zb := psi_z₀_eq ψ hψk hperf D hopp hsl2 hzbc hΦF hcard hP
  have htrans := trans_of_cover ψ hΦF hsingle
  have hmem : ∀ {R : Subgroup K}, R ∈ 𝓕 → R.map ψ ∈ Φ := fun hR =>
    member_map_mem ψ hΦ hsingle hmeets hR
  have hinj : ∀ {R : Subgroup K}, R ∈ 𝓕 → ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := fun {R} hR =>
    injOn_member ψ (hsl2 R hR).some (hcard _ (hmem hR))
  obtain ⟨Ra, Rb, Rc, a, b, u, c, hRa, hRb, hRc, hUa, hUb, hUc, huR, hu4, huu, hau, hab, hc,
    hnc, hgen⟩ := exists_kframe hodd D hV
  have hzcen : z₀ ∈ Subgroup.center K := D.ker_le D.z_mem
  have hUb' := isUniqueInvolution_map_of_inj ψ (hinj hRb) hUb
  refine ⟨Ra.map ψ, hmem hRa, ψ a, isUniqueInvolution_map_of_inj ψ (hinj hRa) hUa,
    Rb.map ψ, hmem hRb, ψ b, ψ u, hUb', ?_, ?_, ?_, Subgroup.mem_map_of_mem ψ huR, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro h
    apply hnc
    apply hψk
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  · intro h
    have hk : b * a⁻¹ * z₀⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h, hz₀]
      group
    apply hnc
    have := Subgroup.mul_mem _ (hψk hk) hzcen
    simpa using this
  · rw [← map_mul, ← map_mul, hab]
  · have h1 : ¬ ψ u ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, ← map_mul, huu]; exact hUb'.ne_one
    have h2 : ψ u ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two (ψ u), ← map_mul, huu,
        pow_two, hUb'.sq]
    simpa using orderOf_eq_prime_pow h1 h2
  · rw [← map_mul, huu]
  · rw [← map_mul, ← map_mul, hau]
  · rcases hc with hc | hc
    · refine ⟨Rc.map ψ, hmem hRc, ?_⟩
      have := isUniqueInvolution_map_of_inj ψ (hinj hRc) hUc
      rwa [hc, map_mul] at this
    · obtain ⟨M', hM', hUM'⟩ := claimZ hΦ hzbc htrans hP (hmem hRc)
        (isUniqueInvolution_map_of_inj ψ (hinj hRc) hUc)
      refine ⟨M', hM', ?_⟩
      have e : ψ a * ψ b = zb * ψ c := by
        rw [← map_mul, hc, map_mul, hz₀]
        exact (Subgroup.mem_center_iff.mp hzbc (ψ c))
      rwa [e]
  · simpa [map_mul] using sup_centralizer_eq_top_of_map ψ hψs hgen

end Cover

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
