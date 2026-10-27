module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G]

@[expose] def liftSub {L : Subgroup G} (F : Subgroup (L ⧸ center L)) : Subgroup G :=
  (F.comap (QuotientGroup.mk' (center L))).map L.subtype

theorem mem_liftSub {L : Subgroup G} {F : Subgroup (L ⧸ center L)} {g : G} :
    g ∈ liftSub F ↔ ∃ l : L, (l : G) = g ∧ (l : L ⧸ center L) ∈ F := by
  simp only [liftSub, Subgroup.mem_map, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    Subgroup.coe_subtype]
  exact ⟨fun ⟨l, hl, e⟩ => ⟨l, e, hl⟩, fun ⟨l, e, hl⟩ => ⟨l, hl, e⟩⟩

theorem liftSub_le {L : Subgroup G} (F : Subgroup (L ⧸ center L)) : liftSub F ≤ L := by
  intro g hg
  obtain ⟨l, rfl, -⟩ := mem_liftSub.1 hg
  exact l.2

structure OutData (L : Subgroup G) (z t : G) (T₁ : Subgroup (centralizer ({z} : Set G)))
    (F : Subgroup (L ⧸ center L)) (tb : L ⧸ center L) : Prop where
  cfg : OuterConfig G L z t (T₁.map (centralizer ({z} : Set G)).subtype)
  Zbot : center L = ⊥
  ker : ∀ g : centralizer ({z} : Set G), thetaH cfg.cent_le g = 1 ↔ (g : G) ∈ zpowers z
  W : SylowWitness (L ⧸ center L) (T₁.map (thetaH cfg.cent_le)) tb F
  tlift : ∃ t' : L, (t' : L ⧸ center L) = tb ∧ (t' : G) = t

variable {L : Subgroup G} {z t : G} {T₁ : Subgroup (centralizer ({z} : Set G))}
  {F : Subgroup (L ⧸ center L)} {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem l_mem_H {l : G} (hl : l ∈ L) : l ∈ centralizer ({z} : Set G) :=
  mem_centralizer_singleton_iff.2 (D.cfg.z_comm_of_mem_A hl)

include D in
theorem conj_mem_L {y : G} (hy : y ∈ centralizer ({z} : Set G)) {l : G} (hl : l ∈ L) :
    y * l * y⁻¹ ∈ L :=
  (mem_normalizer_iff.1 (D.cfg.cent_le hy) l).1 hl

include D in
theorem theta_apply_mk {y : G} (hy : y ∈ centralizer ({z} : Set G)) (l : L) :
    thetaH D.cfg.cent_le ⟨y, hy⟩ (l : L ⧸ center L) =
      ((⟨y * (l : G) * y⁻¹, D.conj_mem_L hy l.2⟩ : L) : L ⧸ center L) :=
  thetaH_apply D.cfg.cent_le ⟨y, hy⟩ l _ rfl

include D in
theorem mk_injective {a b : L} (h : (a : L ⧸ center L) = b) : a = b := by
  rw [QuotientGroup.eq, D.Zbot, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.1 h

include D in
theorem card_liftSub (hF : Nat.card F = 16) : Nat.card (liftSub F) = 16 := by
  have hinj : Function.Injective (QuotientGroup.mk' (center L)) := fun a b h => D.mk_injective h
  let κe : L ≃* L ⧸ center L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have h1 : F.comap (QuotientGroup.mk' (center L)) = F.map κe.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm κe F
  rw [liftSub, Subgroup.card_map_of_injective L.subtype_injective, h1,
    Subgroup.card_map_of_injective κe.symm.injective, hF]

include D in
theorem liftSub_sq (hsq : ∀ x ∈ F, x * x = 1) : ∀ g ∈ liftSub F, g * g = 1 := by
  intro g hg
  obtain ⟨l, rfl, hl⟩ := mem_liftSub.1 hg
  have : ((l * l : L) : L ⧸ center L) = ((1 : L) : L ⧸ center L) := by
    rw [QuotientGroup.mk_mul]; exact hsq _ hl
  have h2 := D.mk_injective this
  simpa using congrArg Subtype.val h2

include D in
theorem liftSub_comm (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    ∀ a ∈ liftSub F, ∀ b ∈ liftSub F, a * b = b * a := by
  intro a ha b hb
  obtain ⟨l, rfl, hl⟩ := mem_liftSub.1 ha
  obtain ⟨l', rfl, hl'⟩ := mem_liftSub.1 hb
  have : ((l * l' : L) : L ⧸ center L) = ((l' * l : L) : L ⧸ center L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc _ hl _ hl'
  have h2 := D.mk_injective this
  simpa using congrArg Subtype.val h2


@[expose] def zH (z : G) : centralizer ({z} : Set G) := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

include D in
theorem zH_mem_T₁ : zH z ∈ T₁ := by
  obtain ⟨y, hy, hyz⟩ := D.cfg.z_mem
  have : y = zH z := Subtype.ext hyz
  rwa [← this]

include D in
theorem mem_T₁_of_theta {g y : centralizer ({z} : Set G)} (hy : y ∈ T₁)
    (h : thetaH D.cfg.cent_le g = thetaH D.cfg.cent_le y) : g ∈ T₁ := by
  have h1 : y⁻¹ * g ∈ (thetaH D.cfg.cent_le).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (D.ker _).1 h1
  have h3 : (y⁻¹ * g) ∈ T₁ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have : y⁻¹ * g = (zH z) ^ k := Subtype.ext (by simpa [zH] using hk.symm)
    rw [this]
    exact Subgroup.zpow_mem _ (D.zH_mem_T₁) k
  have := T₁.mul_mem hy h3
  simpa using this

include D in
theorem theta_conj (l : L) :
    thetaH D.cfg.cent_le ⟨(l : G), D.l_mem_H l.2⟩ = MulAut.conj (l : L ⧸ center L) :=
  thetaH_conj D.cfg.cent_le D.cfg.z_cent l

include D in
theorem liftSub_le_T₁ : ∀ g ∈ liftSub F, ∃ h : g ∈ centralizer ({z} : Set G),
    (⟨g, h⟩ : centralizer ({z} : Set G)) ∈ T₁ := by
  intro g hg
  obtain ⟨l, rfl, hl⟩ := mem_liftSub.1 hg
  refine ⟨D.l_mem_H l.2, ?_⟩
  have hS : MulAut.conj (l : L ⧸ center L) ∈ T₁.map (thetaH D.cfg.cent_le) :=
    D.W.e16.inner_le ⟨(l : L ⧸ center L), hl, rfl⟩
  obtain ⟨y, hy, hyθ⟩ := hS
  exact D.mem_T₁_of_theta hy (by rw [hyθ, D.theta_conj])

include D in
theorem T₁_normalizes_lift {y : centralizer ({z} : Set G)} (hy : y ∈ T₁) {a : G}
    (ha : a ∈ liftSub F) : (y : G) * a * (y : G)⁻¹ ∈ liftSub F := by
  obtain ⟨l, rfl, hl⟩ := mem_liftSub.1 ha
  refine mem_liftSub.2 ⟨⟨(y : G) * l * (y : G)⁻¹, D.conj_mem_L y.2 l.2⟩, rfl, ?_⟩
  have h1 := D.theta_apply_mk y.2 l
  have h2 := (D.W.e16.normal (thetaH D.cfg.cent_le y) ⟨y, hy, rfl⟩ _).1 hl
  rw [show y = ⟨(y : G), y.2⟩ from rfl, h1] at h2
  exact h2

include D in
theorem cent_E1 {y : centralizer ({z} : Set G)}
    (hc : ∀ e ∈ (liftSub F ⊔ zpowers z : Subgroup G), (y : G) * e = e * y) :
    (y : G) ∈ (liftSub F ⊔ zpowers z : Subgroup G) := by
  have hfix : ∀ x ∈ F, thetaH D.cfg.cent_le y x = x := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl : (l : G) ∈ liftSub F := mem_liftSub.2 ⟨l, rfl, hx⟩
    have h1 := D.theta_apply_mk y.2 l
    have h2 : (y : G) * l * (y : G)⁻¹ = l := by
      rw [hc l (mem_sup_left hl)]
      group
    have h3 : (⟨(y : G) * l * (y : G)⁻¹, D.conj_mem_L y.2 l.2⟩ : L) = l := Subtype.ext h2
    rw [show y = ⟨(y : G), y.2⟩ from rfl, h1, h3]
  obtain ⟨x, hx, hxθ⟩ := D.W.e16.cent _ hfix
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective x
  have hl₀ : (l₀ : G) ∈ liftSub F := mem_liftSub.2 ⟨l₀, rfl, hx⟩
  have h1 : thetaH D.cfg.cent_le (y⁻¹ * ⟨(l₀ : G), D.l_mem_H l₀.2⟩) = 1 := by
    rw [map_mul, map_inv, D.theta_conj, hxθ, inv_mul_cancel]
  have h2 := (D.ker _).1 h1
  have h3 : (y : G)⁻¹ * l₀ ∈ zpowers z := h2
  have h4 : (y : G) = l₀ * ((y : G)⁻¹ * l₀)⁻¹ := by group
  rw [h4]
  exact Subgroup.mul_mem _ (mem_sup_left hl₀) (mem_sup_right (Subgroup.inv_mem _ h3))

include D in
theorem disjoint_liftSub_zpowers : Disjoint (liftSub F) (zpowers z) :=
  D.cfg.disjoint.mono_left (liftSub_le F)

include D in
theorem card_E1 (hF : Nat.card F = 16) :
    Nat.card ↥(liftSub F ⊔ zpowers z : Subgroup G) = 32 := by
  have hle := liftSub_le F
  have e := mulEquivProdSup (A := liftSub F) (B := zpowers z)
    (zpowers_le.2 (mem_centralizer_iff.2 fun a ha => D.cfg.z_comm_of_mem_A (hle ha)))
    D.disjoint_liftSub_zpowers
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, D.card_liftSub hF, Nat.card_zpowers,
    D.cfg.z_order]

include D in
theorem E1_comm (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    ∀ a ∈ (liftSub F ⊔ zpowers z : Subgroup G), ∀ b ∈ (liftSub F ⊔ zpowers z : Subgroup G),
      a * b = b * a := by
  have hle := liftSub_le F
  have hcz : zpowers z ≤ centralizer (liftSub F : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => D.cfg.z_comm_of_mem_A (hle ha))
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcz ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcz hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha₂
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb₂
  have hz1 : Commute z a₁ := (D.cfg.z_comm_of_mem_A (hle ha₁)).symm
  have hz2 : Commute z b₁ := (D.cfg.z_comm_of_mem_A (hle hb₁)).symm
  have h12 : Commute a₁ b₁ := D.liftSub_comm hc a₁ ha₁ b₁ hb₁
  have h3 : Commute a₁ (b₁ * z ^ m) := h12.mul_right (hz1.symm.zpow_right m)
  have h4 : Commute (z ^ k) (b₁ * z ^ m) :=
    (hz2.zpow_left k).mul_right ((Commute.refl z).zpow_zpow k m)
  exact (h3.mul_left h4).eq

include D in
theorem orbit8_lift : ∃ l : L, (l : L ⧸ center L) ∈ F ∧ (l : L ⧸ center L) ≠ 1 ∧
    {g : G | ∃ y ∈ T₁, g = (y : G) * l * (y : G)⁻¹}.ncard = 8 := by
  classical
  obtain ⟨x, hx, hx1, h8⟩ := D.W.e16.orbit8
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨l, hx, hx1, ?_⟩
  set O : Set G := {g : G | ∃ y ∈ T₁, g = (y : G) * l * (y : G)⁻¹} with hO
  let Ψ : G → L ⧸ center L := fun h => if hL : h ∈ L then ((⟨h, hL⟩ : L) : L ⧸ center L) else 1
  have hΨL : ∀ (h : G) (hL : h ∈ L), Ψ h = ((⟨h, hL⟩ : L) : L ⧸ center L) := fun h hL => by
    simp [Ψ, hL]
  have hΨ : ∀ (y : centralizer ({z} : Set G)),
      Ψ ((y : G) * l * (y : G)⁻¹) = thetaH D.cfg.cent_le y (l : L ⧸ center L) := by
    intro y
    rw [hΨL _ (D.conj_mem_L y.2 l.2), show y = ⟨(y : G), y.2⟩ from rfl, D.theta_apply_mk y.2 l]
  have himg : autOrbit (T₁.map (thetaH D.cfg.cent_le)) (l : L ⧸ center L) = Ψ '' O := by
    ext w
    constructor
    · rintro ⟨α, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨(y : G) * l * (y : G)⁻¹, ⟨y, hy, rfl⟩, hΨ y⟩
    · rintro ⟨g, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨thetaH D.cfg.cent_le y, ⟨y, hy, rfl⟩, hΨ y⟩
  have hinj : Set.InjOn Ψ O := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    rw [hΨL _ (D.conj_mem_L y.2 l.2), hΨL _ (D.conj_mem_L y'.2 l.2)] at h
    have := D.mk_injective h
    exact congrArg Subtype.val this
  rw [← h8, himg, Set.InjOn.ncard_image hinj]

end OutData


end CFSG.EvenSporadicStandard.M22Std
