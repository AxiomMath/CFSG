module

public import CFSG.ClassicalInvolution.Asc77.AscT8RepEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8V

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W W4 : Subgroup G}

@[expose] def U4E (W4 : Subgroup G) (ρ : Rep Ω W) : Subgroup G := ρ.K ⊓ W4

@[expose] def UUE (W4 : Subgroup G) {ι : Type*} (ρ : ι → Rep Ω W) (S : Set ι) : Subgroup G :=
  Subgroup.closure {x | ∃ s ∈ S, x ∈ U4E W4 (ρ s)}

structure CliqueHooks (Ω : Set (Subgroup G)) (W W4 : Subgroup G) : Prop extends RepHooks Ω W where
  W4_le : W4 ≤ W
  conj_mem_W4 : ∀ {r : G}, r ∈ Subgroup.normalizer (W : Set G) → ∀ {x : G}, x ∈ W4 →
    r * x * r⁻¹ ∈ W4
  img_eq_of_K_eq : ∀ ρ σ : Rep Ω W, ρ.K = σ.K → ρ.img = σ.img
  K_eq_of_img_eq : ∀ ρ σ : Rep Ω W, ρ.img = σ.img → ρ.K = σ.K
  omega_of_comm : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → ρ.img * σ.img = σ.img * ρ.img →
    σ.K ∈ omegaNbr Ω ρ.K
  comm_of_omega : ∀ ρ σ : Rep Ω W, σ.K ∈ omegaNbr Ω ρ.K → ρ.img * σ.img = σ.img * ρ.img
  comm_mem : ∀ ρ σ : Rep Ω W, ρ.K ≠ σ.K → ∀ {v : G}, v ∈ σ.K ⊓ W →
    ρ.r * v * ρ.r⁻¹ * v⁻¹ ∈ ρ.K ⊓ W
  conjInv : ∀ (g : G) (K : Subgroup G), K ∈ Ω → conjSub g K ∈ Ω
  conjD : ∀ {R : Subgroup G}, R ∈ DSet Ω W → ∀ {n : G}, n ∈ Subgroup.normalizer (W : Set G) →
    conjSub n R ∈ DSet Ω W

theorem two_mul_card_le_of_le_of_neE {Q : Type*} [Group Q] [Finite Q] {H₀ H₁ : Subgroup Q}
    (hle : H₀ ≤ H₁) (hne : H₀ ≠ H₁) : 2 * Nat.card H₀ ≤ Nat.card H₁ := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have h0 : 0 < Nat.card H₀ := Nat.card_pos
  have h1 : 0 < Nat.card H₁ := Nat.card_pos
  have hm1 : m ≠ 1 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, h, mul_one]))
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hm2 : 2 ≤ m := by omega
  rw [hm]
  exact Nat.mul_le_mul_left _ hm2 |>.trans' (by omega)

theorem U4_le_WE (H : CliqueHooks Ω W W4)
    (ρ : Rep Ω W) : U4E W4 ρ ≤ W :=
  fun _ hx => H.W4_le hx.2

theorem mem_inf_of_mem_U4E (H : CliqueHooks Ω W W4)
    {ρ : Rep Ω W} {x : G} (hx : x ∈ U4E W4 ρ) : x ∈ ρ.K ⊓ W :=
  ⟨hx.1, H.W4_le hx.2⟩

theorem U4_le_UUE (_H : CliqueHooks Ω W W4)
    {ι : Type*} (ρ : ι → Rep Ω W) {S : Set ι} {s : ι} (hs : s ∈ S) :
    U4E W4 (ρ s) ≤ UUE W4 ρ S :=
  fun _ hx => Subgroup.subset_closure ⟨s, hs, hx⟩

theorem UU_le_W4E (_H : CliqueHooks Ω W W4)
    {ι : Type*} (ρ : ι → Rep Ω W) (S : Set ι) : UUE W4 ρ S ≤ W4 := by
  rw [UUE, Subgroup.closure_le]
  rintro x ⟨s, -, hx⟩
  exact hx.2

theorem conj_mem_U4E (H : CliqueHooks Ω W W4)
    (ρ σ : Rep Ω W) {x : G} (hx : x ∈ U4E W4 σ) :
    ρ.r * x * ρ.r⁻¹ ∈ U4E W4 ρ ⊔ U4E W4 σ := by
  have hrN := ρ.r_mem_normalizer
  have hxW : x ∈ σ.K ⊓ W := mem_inf_of_mem_U4E H hx
  by_cases hK : ρ.K = σ.K
  · have hxρ : x ∈ ρ.K ⊓ W := by rw [hK]; exact hxW
    rw [H.conj_inv ρ hxρ]
    exact Subgroup.mem_sup_right ((U4E W4 σ).inv_mem hx)
  · have hcomm := H.comm_mem ρ σ hK hxW
    have e1 : ρ.r * x * ρ.r⁻¹ * x⁻¹ ∈ U4E W4 ρ :=
      ⟨hcomm.1, W4.mul_mem (H.conj_mem_W4 hrN hx.2) (W4.inv_mem hx.2)⟩
    have e2 : ρ.r * x * ρ.r⁻¹ = (ρ.r * x * ρ.r⁻¹ * x⁻¹) * x := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left e1) (Subgroup.mem_sup_right hx)

theorem normalizes_UUE (H : CliqueHooks Ω W W4)
    {ι : Type*} (ρ : ι → Rep Ω W) {S : Set ι} {s : ι} (hs : s ∈ S) :
    (ρ s).r ∈ Subgroup.normalizer ((UUE W4 ρ S : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_le
  have key : ∀ x ∈ UUE W4 ρ S, (ρ s).r * x * (ρ s).r⁻¹ ∈ UUE W4 ρ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, hyt⟩ := hy
      have := conj_mem_U4E H (ρ s) (ρ t) hyt
      exact (sup_le (U4_le_UUE H ρ hs) (U4_le_UUE H ρ ht)) this
    | one => simp
    | mul y z _ _ hy hz =>
      have e : (ρ s).r * (y * z) * (ρ s).r⁻¹ =
          ((ρ s).r * y * (ρ s).r⁻¹) * ((ρ s).r * z * (ρ s).r⁻¹) := by group
      rw [e]
      exact (UUE W4 ρ S).mul_mem hy hz
    | inv y _ hy =>
      have e : (ρ s).r * y⁻¹ * (ρ s).r⁻¹ = ((ρ s).r * y * (ρ s).r⁻¹)⁻¹ := by group
      rw [e]
      exact (UUE W4 ρ S).inv_mem hy
  rintro _ ⟨x, hx, rfl⟩
  exact key x hx

theorem exists_mul_of_mem_UU_insertE (H : CliqueHooks Ω W W4)
    {ι : Type*} (ρ : ι → Rep Ω W) {B : Set ι} {a : ι} {g : G}
    (hg : g ∈ UUE W4 ρ (insert a B)) :
    ∃ x ∈ U4E W4 (ρ a), ∃ a₁ ∈ UUE W4 ρ B, g = x * a₁ := by
  have hcomm : ∀ x ∈ U4E W4 (ρ a), ∀ y ∈ UUE W4 ρ B, x * y = y * x := fun x hx y hy =>
    H.comm_W x (U4_le_WE H _ hx) y (H.W4_le (UU_le_W4E H ρ B hy))
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨t, ht, hyt⟩ := hy
    rcases ht with rfl | ht
    · exact ⟨y, hyt, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨1, Subgroup.one_mem _, y, U4_le_UUE H ρ ht hyt, by simp⟩
  | one => exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨x, hx, a₁, ha₁, rfl⟩ := hy
    obtain ⟨x', hx', a₁', ha₁', rfl⟩ := hz
    refine ⟨x * x', (U4E W4 (ρ a)).mul_mem hx hx', a₁ * a₁', (UUE W4 ρ B).mul_mem ha₁ ha₁', ?_⟩
    calc x * a₁ * (x' * a₁') = x * (a₁ * x') * a₁' := by simp only [mul_assoc]
      _ = x * (x' * a₁) * a₁' := by rw [← hcomm x' hx' a₁ ha₁]
      _ = x * x' * (a₁ * a₁') := by simp only [mul_assoc]
  | inv y _ hy =>
    obtain ⟨x, hx, a₁, ha₁, rfl⟩ := hy
    refine ⟨x⁻¹, (U4E W4 (ρ a)).inv_mem hx, a₁⁻¹, (UUE W4 ρ B).inv_mem ha₁, ?_⟩
    rw [mul_inv_rev]
    exact (Commute.inv_inv (show Commute x a₁ from hcomm x hx a₁ ha₁)).eq.symm

theorem rep_K_neE (H : CliqueHooks Ω W W4) (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) : (rep x).K ≠ (rep y).K := by
  intro h
  apply hne
  have := H.img_eq_of_K_eq (rep x) (rep y) h
  rw [hrep x hx, hrep y hy] at this
  exact Subtype.ext this

theorem rep_omegaE (H : CliqueHooks Ω W W4) (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) (hcomm : x * y = y * x) : (rep y).K ∈ omegaNbr Ω (rep x).K := by
  refine H.omega_of_comm (rep x) (rep y) (rep_K_neE H rep hrep hx hy hne) ?_
  rw [hrep x hx, hrep y hy]
  exact congrArg Subtype.val hcomm

theorem rep_noncommE (H : CliqueHooks Ω W W4) (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hnc : x * y ≠ y * x) : (rep x).K ≠ (rep y).K ∧ (rep y).K ∉ omegaNbr Ω (rep x).K := by
  refine ⟨fun h => hnc ?_, fun hnbr => hnc ?_⟩
  · have := H.img_eq_of_K_eq (rep x) (rep y) h
    rw [hrep x hx, hrep y hy] at this
    rw [Subtype.ext this]
  · have := H.comm_of_omega (rep x) (rep y) hnbr
    rw [hrep x hx, hrep y hy] at this
    exact Subtype.ext this

theorem centralizes_UUE (H : CliqueHooks Ω W W4) (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {x : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) {S : Set ↥(muGroup Ω W)}
    (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    ∀ g ∈ UUE W4 rep S, (rep x).r * g * (rep x).r⁻¹ = g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, hys⟩ := hy
    obtain ⟨hsΔ, hxs, hcomm⟩ := hS s hs
    have hnbr := rep_omegaE H rep hrep hx hsΔ hxs hcomm
    have := H.centralizes (rep x) (rep s) hnbr (mem_inf_of_mem_U4E H hys)
    rw [this]
    group
  | one => simp
  | mul y z _ _ hy hz =>
    have e : (rep x).r * (y * z) * (rep x).r⁻¹ =
        ((rep x).r * y * (rep x).r⁻¹) * ((rep x).r * z * (rep x).r⁻¹) := by group
    rw [e, hy, hz]
  | inv y _ hy =>
    have e : (rep x).r * y⁻¹ * (rep x).r⁻¹ = ((rep x).r * y * (rep x).r⁻¹)⁻¹ := by group
    rw [e, hy]

theorem U4_le_UU_of_generatesE (H : CliqueHooks Ω W W4) (rep : ↥(muGroup Ω W) → Rep Ω W)
    (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
    {a d : ↥(muGroup Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W) (haΔ : a ∈ muDelta Ω W) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hconj : ∀ y ∈ muDelta Ω W, ∃ q : ↥(muGroup Ω W), y = q * d * q⁻¹)
    {y : ↥(muGroup Ω W)} (hy : y ∈ muDelta Ω W) :
    U4E W4 (rep y) ≤ UUE W4 rep (insert a (↑B : Set ↥(muGroup Ω W))) := by
  set S : Set ↥(muGroup Ω W) := insert a ↑B with hS
  have hSΔ : S ⊆ muDelta Ω W := Set.insert_subset haΔ hBΔ
  set W₀ := UUE W4 rep S with hW₀
  obtain ⟨q, hq⟩ := hconj y hy
  set L : Set G := {g | ∃ s ∈ S, g = (rep s).r} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact (rep s).r_mem_normalizer
  have hLW₀ : Subgroup.closure L ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact normalizes_UUE H rep hs
  have hq' : (q : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    have hmem : q ∈ Subgroup.closure S := by rw [hgen]; trivial
    have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hmem
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(rep s).r, ⟨s, hs, rfl⟩, hrep s (hSΔ hs)⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := ((Subgroup.closure_le _).mpr hLN) hg
  have hgW₀ : g ∈ Subgroup.normalizer (W₀ : Set G) := hLW₀ hg
  have hdΔ : d ∈ muDelta Ω W := hBΔ (Finset.mem_coe.mpr hdB)
  let σ : Rep Ω W :=
    { K := conjSub g (rep d).K
      R := conjSub g (rep d).R
      r := g * (rep d).r * g⁻¹
      hK := H.conjInv g _ (rep d).hK
      hR := H.conjD (rep d).hR hgN
      hRK := (rep d).hRK.conj g
      hr := conj_mem_conjSub (rep d).hr
      hrW := fun h => (rep d).hrW ((mem_normalizer_iff_of_mem hgN _).mp h) }
  have himg : σ.img = (rep y).img := by
    show piG W (g * (rep d).r * g⁻¹) = (rep y).img
    rw [piG_mul (Subgroup.mul_mem _ hgN (rep d).r_mem_normalizer) (Subgroup.inv_mem _ hgN),
      piG_mul hgN (rep d).r_mem_normalizer, piG_inv hgN, hgq]
    have h1 : piG W (rep d).r = (d : NQuot (W ⊔ OCW W)) := hrep d hdΔ
    have h2 : (y : NQuot (W ⊔ OCW W)) =
        (q : NQuot (W ⊔ OCW W)) * d * (q : NQuot (W ⊔ OCW W))⁻¹ := by
      rw [hq]
      rfl
    rw [h1, hrep y hy, h2]
  have hKσ : σ.K = (rep y).K := H.K_eq_of_img_eq σ (rep y) himg
  intro x hx
  have hxσ' : x ∈ σ.K := by rw [hKσ]; exact hx.1
  have hxσ : x ∈ conjSub g (rep d).K := hxσ'
  rw [mem_conjSub_iff] at hxσ
  have hx4 : g⁻¹ * x * g ∈ W4 := by
    have := H.conj_mem_W4 (Subgroup.inv_mem _ hgN) hx.2
    simpa using this
  have hmem : g⁻¹ * x * g ∈ W₀ :=
    U4_le_UUE H rep (Set.mem_insert_of_mem a (Finset.mem_coe.mpr hdB))
      ⟨hxσ, hx4⟩
  have := (Subgroup.mem_normalizer_iff.mp hgW₀ _).mp hmem
  simpa [mul_assoc] using this

theorem two_pow_card_le_closureE
    (hnm : ∀ {x : ↥(muGroup Ω W)}, x ∈ muDelta Ω W → ∀ {S : Set ↥(muGroup Ω W)},
      (∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) → x ∉ Subgroup.closure S)
    (S : Finset ↥(muGroup Ω W))
    (hS : ∀ x ∈ S, x ∈ muDelta Ω W)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    2 ^ S.card ≤ Nat.card ↥(Subgroup.closure (↑S : Set ↥(muGroup Ω W))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, pow_zero, Finset.coe_empty]
    exact Nat.card_pos
  | insert x S₀ hx ih =>
    have hS₀ : ∀ y ∈ S₀, y ∈ muDelta Ω W := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have hcomm₀ : ∀ y ∈ S₀, ∀ z ∈ S₀, y * z = z * y := fun y hy z hz =>
      hcomm y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    have ih' := ih hS₀ hcomm₀
    have hxΔ : x ∈ muDelta Ω W := hS x (Finset.mem_insert_self x S₀)
    have hnot : x ∉ Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) :=
      hnm hxΔ fun s hs =>
        ⟨hS₀ s hs, fun e => hx (e ▸ hs), hcomm x (Finset.mem_insert_self x S₀) s
          (Finset.mem_insert_of_mem hs)⟩
    have hle : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≤
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) :=
      Subgroup.closure_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hne : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≠
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) := fun e =>
      hnot (e ▸ Subgroup.subset_closure (by rw [Finset.coe_insert]; exact Set.mem_insert _ _))
    have := two_mul_card_le_of_le_of_neE hle hne
    rw [Finset.card_insert_of_notMem hx, pow_succ]
    omega

end T8V

end CFSG.ClassicalInvolution.Asc77
