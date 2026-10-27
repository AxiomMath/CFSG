module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

namespace Twin1711

section Transport

variable {H G : Type} [Group H] [Group G]

theorem comap_conjSub (ψ : H →* G) (s : H) (J : Subgroup G) :
    (conjSub (ψ s) J).comap ψ = conjSub s (J.comap ψ) := by
  ext y
  rw [Subgroup.mem_comap, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_comap]
  simp [map_mul, map_inv]

theorem comap_injOn {ψ : H →* G} :
    Set.InjOn (Subgroup.comap ψ) {J : Subgroup G | J ≤ ψ.range} := by
  intro J1 h1 J2 h2 h
  rw [← Subgroup.map_comap_eq_self h1, ← Subgroup.map_comap_eq_self h2, h]

theorem conjSub_le_range {ψ : H →* G} {R : Subgroup G} (hR : R ≤ ψ.range) {x : G}
    (hx : x ∈ ψ.range) : conjSub x R ≤ ψ.range := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := hR hy
  have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [this]
  exact ψ.range.mul_mem (ψ.range.mul_mem hx h1) (ψ.range.inv_mem hx)

theorem uniqueInv_of_comap {ψ : H →* G} (hψ : Function.Injective ψ) {J : Subgroup G}
    {u : G} (h : IsUniqueInvolution J u) {u' : H} (hu : ψ u' = u) :
    IsUniqueInvolution (J.comap ψ) u' where
  mem := by rw [Subgroup.mem_comap, hu]; exact h.mem
  ne_one := by
    intro h1
    apply h.ne_one
    rw [← hu, h1, map_one]
  sq := hψ (by rw [map_mul, hu, map_one]; exact h.sq)
  unique := by
    intro y hy hy2
    rw [Subgroup.mem_comap] at hy
    have h2 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases h.unique _ hy h2 with h1 | h1
    · left
      exact hψ (by rw [h1, map_one])
    · right
      exact hψ (by rw [h1, hu])

theorem psi_mem_T {ψ : H →* G} {t' : H} {t : G} (ht' : ψ t' = t) {s : H}
    (hs : s ∈ (⊤ : Subgroup H) ⊓ Subgroup.centralizer ({t'} : Set H)) :
    ψ s ∈ ψ.range ⊓ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_inf] at hs ⊢
  refine ⟨⟨s, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rw [← ht', ← map_mul, ← map_mul]
  exact congrArg ψ (Subgroup.mem_centralizer_iff.mp hs.2 t' rfl)

theorem mem_T_of_psi {ψ : H →* G} (hψ : Function.Injective ψ) {t' : H} {t : G}
    (ht' : ψ t' = t) {s : H}
    (hs : ψ s ∈ ψ.range ⊓ Subgroup.centralizer ({t} : Set G)) :
    s ∈ (⊤ : Subgroup H) ⊓ Subgroup.centralizer ({t'} : Set H) := by
  rw [Subgroup.mem_inf] at hs ⊢
  refine ⟨Subgroup.mem_top _, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply hψ
  rw [map_mul, map_mul, ht']
  exact Subgroup.mem_centralizer_iff.mp hs.2 t rfl

variable {ψ : H →* G}

theorem CoreData.comap {R : Subgroup G} {t : G} (h : CoreData ψ.range R t)
    (hψ : Function.Injective ψ) {t' : H} (ht' : ψ t' = t) :
    CoreData (⊤ : Subgroup H) (R.comap ψ) t' where
  le := le_top
  q8 := by
    obtain ⟨e⟩ := h.q8
    refine ⟨MulEquiv.trans (MulEquiv.ofBijective (ψ.subgroupComap R) ⟨?_, ?_⟩) e⟩
    · intro a b hab
      apply Subtype.ext
      apply hψ
      exact congrArg Subtype.val hab
    · intro y
      obtain ⟨x, hx⟩ := h.le y.2
      exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  inv := uniqueInv_of_comap hψ h.inv ht'
  noncentral := by
    intro hc
    apply h.noncentral
    intro x hx
    obtain ⟨x', rfl⟩ := hx
    rw [← ht', ← map_mul, ← map_mul]
    exact congrArg ψ (hc x' (Subgroup.mem_top _))
  inO2 := by
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := h.inO2
    refine ⟨P.comap ψ, ?_, ?_, ?_, Subgroup.comap_mono hP4⟩
    · intro x hx
      rw [Subgroup.mem_comap] at hx
      exact mem_T_of_psi hψ ht' (hP1 hx)
    · intro s hs p hp
      rw [Subgroup.mem_comap] at hp ⊢
      have := hP2 (ψ s) (psi_mem_T ht' hs) (ψ p) hp
      simpa [map_mul, map_inv] using this
    · have hinj : Function.Injective (ψ.subgroupComap P) := by
        intro a b hab
        apply Subtype.ext
        apply hψ
        exact congrArg Subtype.val hab
      exact hP3.of_injective _ hinj
  twins := by
    intro s hs
    have hT := psi_mem_T ht' hs
    rw [← comap_conjSub]
    rcases h.twins (ψ s) hT with h1 | h1
    · left
      rw [h1]
    · right
      intro a ha b hb
      rw [Subgroup.mem_comap] at ha hb
      exact hψ (by rw [map_mul, map_mul]; exact h1 _ ha _ hb)

theorem block_le_range {X R : Subgroup G} {t : G} {B : Set (Subgroup G)} {N : Subgroup G}
    (hS : SandwichData X R t B N) (hR : R ≤ X) {J : Subgroup G} (hJ : J ∈ B) : J ≤ X := by
  obtain ⟨x, hx, rfl⟩ := hS.sub hJ
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := hR hy
  have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [this]
  exact X.mul_mem (X.mul_mem hx h1) (X.inv_mem hx)

theorem SandwichData.comap [Finite H] {R : Subgroup G} {t : G} {B : Set (Subgroup G)}
    {N : Subgroup G} (hR : R ≤ ψ.range) (h : SandwichData ψ.range R t B N)
    (hψ : Function.Injective ψ) {t' : H} (ht' : ψ t' = t) :
    SandwichData (⊤ : Subgroup H) (R.comap ψ) t' ((Subgroup.comap ψ) '' B) (N.comap ψ) where
  mem := ⟨R, h.mem, rfl⟩
  sub := by
    rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := h.sub hJ
    obtain ⟨x0, rfl⟩ := hx
    exact ⟨x0, Subgroup.mem_top _, by rw [← comap_conjSub]⟩
  block := by
    intro x' _
    have hle : ∀ J ∈ B, J ≤ ψ.range := fun J hJ => block_le_range h hR hJ
    have himg : conjSub x' '' ((Subgroup.comap ψ) '' B) =
        (Subgroup.comap ψ) '' (conjSub (ψ x') '' B) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      ext J : 1
      exact (comap_conjSub ψ x' J).symm
    rw [himg]
    rcases h.block (ψ x') ⟨x', rfl⟩ with h1 | h1
    · left
      rw [h1]
    · right
      rw [Set.disjoint_left]
      rintro _ ⟨J1, hJ1, rfl⟩ ⟨J2, hJ2, hJ12⟩
      have hJ1le : J1 ≤ ψ.range := by
        obtain ⟨J0, hJ0, rfl⟩ := hJ1
        exact conjSub_le_range (hle J0 hJ0) ⟨x', rfl⟩
      have : J2 = J1 := comap_injOn (hle J2 hJ2) hJ1le hJ12
      subst this
      exact Set.disjoint_left.mp h1 hJ1 hJ2
  proper := by
    intro hEq
    apply h.proper
    ext J
    constructor
    · exact fun hJ => h.sub hJ
    · intro hJ
      obtain ⟨y, hy, rfl⟩ := hJ
      obtain ⟨y0, rfl⟩ := hy
      have h1 : conjSub y0 (R.comap ψ) ∈ xOrbit (⊤ : Subgroup H) (R.comap ψ) :=
        ⟨y0, Subgroup.mem_top _, rfl⟩
      rw [← hEq] at h1
      obtain ⟨J0, hJ0, hJ0e⟩ := h1
      rw [← comap_conjSub] at hJ0e
      have hle := block_le_range h hR hJ0
      have := comap_injOn hle (conjSub_le_range hR ⟨y0, rfl⟩) hJ0e
      rw [this] at hJ0
      exact hJ0
  twins := by
    intro s hs
    refine ⟨conjSub (ψ s) R, h.twins (ψ s) (psi_mem_T ht' hs), ?_⟩
    exact comap_conjSub ψ s R
  le := by
    intro n hn
    rw [Subgroup.mem_comap] at hn
    exact mem_T_of_psi hψ ht' (h.le hn)
  normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgT := psi_mem_T ht' g.2
    have hnT := psi_mem_T ht' n.2
    have := h.normal.conj_mem ⟨ψ n, hnT⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn)
      ⟨ψ g, hgT⟩
    rw [Subgroup.mem_subgroupOf] at this
    rw [Subgroup.mem_comap]
    simpa [map_mul, map_inv] using this
  t_mem := by rw [Subgroup.mem_comap, ht']; exact h.t_mem
  twins_le := by
    intro s hs
    rw [← comap_conjSub]
    exact Subgroup.comap_mono (h.twins_le (ψ s) (psi_mem_T ht' hs))
  inv := by
    intro x' _ hx'
    rw [Subgroup.mem_comap] at hx'
    have e1 : ψ (x' * t' * x'⁻¹) = ψ x' * t * (ψ x')⁻¹ := by simp [map_mul, map_inv, ht']
    rw [e1] at hx'
    obtain ⟨J, hJ, hJu⟩ := h.inv (ψ x') ⟨x', rfl⟩ hx'
    exact ⟨J.comap ψ, ⟨J, hJ, rfl⟩, uniqueInv_of_comap hψ hJu e1⟩
  index := by
    classical
    refine le_trans ?_ (le_trans h.index ?_)
    · rw [Subgroup.relIndex_comap]
      have hmap : Subgroup.map ψ ((⊤ : Subgroup H) ⊓ Subgroup.centralizer ({t'} : Set H)) =
          ψ.range ⊓ Subgroup.centralizer ({t} : Set G) := by
        ext g
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact psi_mem_T ht' hs
        · intro hg
          obtain ⟨⟨s, rfl⟩, _⟩ := Subgroup.mem_inf.mp hg
          exact ⟨s, mem_T_of_psi hψ ht' hg, rfl⟩
      rw [hmap]
    ·
      let φ : ↥(⊤ : Subgroup H) ≃* ↥ψ.range :=
        Subgroup.topEquiv.trans (MonoidHom.ofInjective hψ)
      let Φ : MulAut ↥ψ.range ≃* MulAut ↥(⊤ : Subgroup H) := (MulAut.congr φ).symm
      have hmem : ∀ α ∈ fixSet ψ.range B, Φ α ∈ fixSet (⊤ : Subgroup H) ((Subgroup.comap ψ) '' B) := by
        intro α hα b' hb' y hy
        obtain ⟨b, hb, rfl⟩ := hb'
        have hy' : ((φ y : ↥ψ.range) : G) ∈ b := by
          rw [Subgroup.mem_comap] at hy
          exact hy
        have h1 := hα b hb (φ y) hy'
        show φ.symm (α (φ y)) = y
        rw [h1]
        exact φ.symm_apply_apply y
      let f : ↥(fixSet ψ.range B) → ↥(fixSet (⊤ : Subgroup H) ((Subgroup.comap ψ) '' B)) :=
        fun α => ⟨Φ α.1, hmem α.1 α.2⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        exact Φ.injective (congrArg Subtype.val hab)
      exact Nat.card_le_card_of_injective f hf

theorem xOrbit_le_range {R : Subgroup G} (hR : R ≤ ψ.range) {J : Subgroup G}
    (hJ : J ∈ xOrbit ψ.range R) : J ≤ ψ.range := by
  obtain ⟨x, hx, rfl⟩ := hJ
  exact conjSub_le_range hR hx

theorem commNbrs_comap {R : Subgroup G} (hR : R ≤ ψ.range) (hψ : Function.Injective ψ) :
    commNbrs (⊤ : Subgroup H) (R.comap ψ) = (Subgroup.comap ψ) '' commNbrs ψ.range R := by
  ext J'
  constructor
  · rintro ⟨⟨x0, -, rfl⟩, hJ⟩
    refine ⟨conjSub (ψ x0) R, ⟨⟨ψ x0, ⟨x0, rfl⟩, rfl⟩, ?_⟩, comap_conjSub ψ x0 R⟩
    rcases hJ with h1 | h1
    · left
      rw [← comap_conjSub] at h1
      exact comap_injOn (conjSub_le_range hR ⟨x0, rfl⟩) hR h1
    · right
      intro a ha b hb
      obtain ⟨a0, rfl⟩ := hR ha
      obtain ⟨b0, rfl⟩ := conjSub_le_range hR ⟨x0, rfl⟩ hb
      have h2 := h1 a0 (by rw [Subgroup.mem_comap]; exact ha) b0
        (by rw [← comap_conjSub, Subgroup.mem_comap]; exact hb)
      rw [← map_mul, ← map_mul, h2]
  · rintro ⟨J, ⟨⟨x, hx, rfl⟩, hJ⟩, rfl⟩
    obtain ⟨x0, rfl⟩ := hx
    refine ⟨⟨x0, Subgroup.mem_top _, (comap_conjSub ψ x0 R).symm⟩, ?_⟩
    rcases hJ with h1 | h1
    · left
      rw [h1]
    · right
      intro a ha b hb
      rw [Subgroup.mem_comap] at ha hb
      exact hψ (by rw [map_mul, map_mul]; exact h1 _ ha _ hb)

@[expose] def NoSandwichIn (H : Type) [Group H] : Prop :=
  ∀ (R : Subgroup H) (t : H) (B : Set (Subgroup H)) (N : Subgroup H),
    CoreData (⊤ : Subgroup H) R t → SandwichData (⊤ : Subgroup H) R t B N → False

@[expose] def SandwichSizeTwoIn (H : Type) [Group H] : Prop :=
  ∀ (R : Subgroup H) (t : H) (B : Set (Subgroup H)) (N : Subgroup H),
    CoreData (⊤ : Subgroup H) R t → SandwichData (⊤ : Subgroup H) R t B N → B.ncard = 2

@[expose] def PairingIn (H : Type) [Group H] : Prop :=
  ∀ (R : Subgroup H) (t : H), CoreData (⊤ : Subgroup H) R t →
    (commNbrs (⊤ : Subgroup H) R).ncard = 4 ∧
      ∀ J ∈ commNbrs (⊤ : Subgroup H) R, ∀ J' ∈ commNbrs (⊤ : Subgroup H) R, J ≠ J' →
        ∀ u u' : H, IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ (⊤ : Subgroup H), x * (u * u') = (u * u') * x

end Transport

theorem exists_inj_range {H G : Type} [Group H] [Group G] {X : Subgroup G} (e : ↥X ≃* H) :
    ∃ ψ : H →* G, Function.Injective ψ ∧ ψ.range = X := by
  refine ⟨X.subtype.comp e.symm.toMonoidHom,
    X.subtype_injective.comp e.symm.injective, ?_⟩
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact (e.symm h).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

theorem noSandwichAt_of_in {H : Type} [Group H] (h : NoSandwichIn H) : NoSandwichAt H := by
  intro G _ _ X R t B N ⟨e⟩ hC hS
  obtain ⟨ψ, hψ, hX⟩ := exists_inj_range e
  subst hX
  obtain ⟨t', ht'⟩ := hC.le hC.inv.mem
  have : Finite H := Finite.of_equiv _ e.toEquiv
  exact h _ t' _ _ (hC.comap hψ ht') (hS.comap hC.le hψ ht')

theorem sandwichSizeTwoAt_of_in {H : Type} [Group H] (h : SandwichSizeTwoIn H) :
    SandwichSizeTwoAt H := by
  intro G _ _ X R t B N ⟨e⟩ hC hS
  obtain ⟨ψ, hψ, hX⟩ := exists_inj_range e
  subst hX
  obtain ⟨t', ht'⟩ := hC.le hC.inv.mem
  have : Finite H := Finite.of_equiv _ e.toEquiv
  have h1 := h _ t' _ _ (hC.comap hψ ht') (hS.comap hC.le hψ ht')
  rw [Set.InjOn.ncard_image] at h1
  · exact h1
  · intro J1 hJ1 J2 hJ2 h12
    exact comap_injOn (block_le_range hS hC.le hJ1) (block_le_range hS hC.le hJ2) h12

theorem pairingAt_of_in {H : Type} [Group H] (h : PairingIn H) : PairingAt H := by
  intro G _ _ X R t ⟨e⟩ hC
  obtain ⟨ψ, hψ, hX⟩ := exists_inj_range e
  subst hX
  obtain ⟨t', ht'⟩ := hC.le hC.inv.mem
  have : Finite H := Finite.of_equiv _ e.toEquiv
  obtain ⟨h4, hpair⟩ := h _ t' (hC.comap hψ ht')
  have hinj : Set.InjOn (Subgroup.comap ψ) (commNbrs ψ.range R) :=
    fun J1 hJ1 J2 hJ2 h12 =>
      comap_injOn (xOrbit_le_range hC.le hJ1.1) (xOrbit_le_range hC.le hJ2.1) h12
  rw [commNbrs_comap hC.le hψ] at h4 hpair
  rw [hinj.ncard_image] at h4
  refine ⟨h4, ?_⟩
  intro J hJ J' hJ' hne u u' hu hu'
  have hJle := xOrbit_le_range hC.le hJ.1
  have hJ'le := xOrbit_le_range hC.le hJ'.1
  obtain ⟨u0, hu0⟩ := hJle hu.mem
  obtain ⟨u0', hu0'⟩ := hJ'le hu'.mem
  obtain ⟨hne', hcomm⟩ := hpair (J.comap ψ) ⟨J, hJ, rfl⟩ (J'.comap ψ) ⟨J', hJ', rfl⟩
    (fun h12 => hne (comap_injOn hJle hJ'le h12)) u0 u0'
    (uniqueInv_of_comap hψ hu hu0) (uniqueInv_of_comap hψ hu' hu0')
  refine ⟨fun h12 => hne' (hψ (by rw [hu0, hu0']; exact h12)), ?_⟩
  intro x hx
  obtain ⟨x0, rfl⟩ := hx
  have := congrArg ψ (hcomm x0 (Subgroup.mem_top _))
  simp only [map_mul, hu0, hu0'] at this
  exact this

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
