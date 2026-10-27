module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMain
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightRes
public import CFSG.CGT.PushingUpLit.BHS.Offender

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS

section Glue

variable {V : Type} [CommGroup V] [Finite V] {E A : Subgroup (MulAut V)} (P : Subgroup V)

omit [Finite V] in
theorem le_stabP_of_invariant {B : Subgroup (MulAut V)} (hB : ∀ b ∈ B, ∀ p ∈ P, b p ∈ P) :
    B ≤ stabP P := fun b hb p hp => ⟨hB b hb p hp, hB b⁻¹ (B.inv_mem hb) p hp⟩

variable {F L : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup L] [Module F L]
  [Module.Finite F L] [Finite L] (D : Data F L)
  (φ : P ≃ Wd F L) (hφ : ∀ p q : P, φ (p * q) = φ p + φ q)

include hφ

omit [Finite V] [Finite F] [CharP F 2] [Module.Finite F L] [Finite L] in
theorem resPerm_isAdd (g : MulAut V) (hg : g ∈ stabP P) : IsAddPerm (resPerm P φ g hg) := by
  intro w w'
  obtain ⟨p, rfl⟩ := φ.surjective w
  obtain ⟨q, rfl⟩ := φ.surjective w'
  rw [← hφ, resPerm_apply, resPerm_apply, resPerm_apply, ← hφ]
  congr 1
  apply Subtype.ext
  show g (p * q : V) = g p * g q
  exact map_mul g _ _

omit [CharP F 2] [Module.Finite F L] hφ in
theorem offender_to_flag (hoff : IsOff A) (hAstab : A ≤ stabP P) :
    Nat.card (Wd F L) ≤ Nat.card ((resHom P φ).comp (Subgroup.inclusion hAstab)).range *
      Nat.card (Fix ((resHom P φ).comp (Subgroup.inclusion hAstab)).range) := by
  classical
  obtain ⟨rA, hrA⟩ : ∃ rA : A →* Equiv.Perm (Wd F L),
      rA = (resHom P φ).comp (Subgroup.inclusion hAstab) := ⟨_, rfl⟩
  rw [← hrA]
  have h1 := offender_card_le hoff P
  have h2 : (fixV A).relIndex P * Nat.card (fixV A ⊓ P : Subgroup V) = Nat.card P :=
    Subgroup.relIndex_mul_card (fixV A) P
  have h3 := relIndex_cenIn_mul_card A P
  have hrAapply : ∀ (a : A) (p : P), rA a (φ p) = φ ⟨a.1 p, (hAstab a.2 p p.2).1⟩ := by
    intro a p
    rw [hrA]
    exact resPerm_apply P φ a.1 (hAstab a.2) p
  have hker : rA.ker = (cenIn A P).subgroupOf A := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cenIn]
    constructor
    · intro h
      refine ⟨ha, fun u hu => ?_⟩
      have := congrArg (fun τ : Equiv.Perm (Wd F L) => τ (φ ⟨u, hu⟩)) h
      simp only [hrAapply, Equiv.Perm.one_apply] at this
      exact congrArg Subtype.val (φ.injective this)
    · rintro ⟨-, h⟩
      ext w : 1
      obtain ⟨p, rfl⟩ := φ.surjective w
      rw [hrAapply]
      simp only [Equiv.Perm.one_apply]
      congr 1
      exact Subtype.ext (h p p.2)
  have h4 : Nat.card rA.range * Nat.card rA.ker = Nat.card A := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup rA.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rA).toEquiv] at this
    exact this.symm
  have h5 : Nat.card rA.ker = Nat.card (cenIn A P) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cenIn_le A P)).toEquiv
  have hpos : 0 < Nat.card (cenIn A P) := Nat.card_pos
  have h6 : (cenIn A P).relIndex A = Nat.card rA.range := by
    rw [h5] at h4
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans h4.symm)
  have h7 : Nat.card (fixV A ⊓ P : Subgroup V) ≤ Nat.card (Fix rA.range) := by
    refine Nat.card_le_card_of_injective
      (fun x : (fixV A ⊓ P : Subgroup V) =>
        (⟨φ ⟨x.1, x.2.2⟩, ?_⟩ : Fix rA.range)) ?_
    · rintro _ ⟨a, rfl⟩
      rw [hrAapply]
      congr 1
      exact Subtype.ext (x.2.1 a.1 a.2)
    · intro x y hxy
      apply Subtype.ext
      have := φ.injective (congrArg (fun z : Fix rA.range => (z : Wd F L)) hxy)
      exact congrArg (fun z : P => (z : V)) this
  calc Nat.card (Wd F L) = Nat.card P := (Nat.card_congr φ).symm
    _ = (fixV A).relIndex P * Nat.card (fixV A ⊓ P : Subgroup V) := h2.symm
    _ ≤ Nat.card rA.range * Nat.card (fixV A ⊓ P : Subgroup V) :=
        Nat.mul_le_mul_right _ (h6 ▸ h1)
    _ ≤ Nat.card rA.range * Nat.card (Fix rA.range) := Nat.mul_le_mul_left _ h7

theorem twoEight_of_model (hoff : IsOff A) (hAE : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E)
    (hPE : ∀ e ∈ E, ∀ p ∈ P, e p ∈ P) (hPA : ∀ a ∈ A, ∀ p ∈ P, a p ∈ P)
    (hF : 3 ≤ Nat.card F)
    {S : Type} [Group S] (θ : ↥E ≃* S) (ΓS : S →* Equiv.Perm (Wd F L))
    (hequiv : ∀ (e : ↥E) (p : P) (hp : (e : MulAut V) p ∈ P),
      φ ⟨(e : MulAut V) p, hp⟩ = ΓS (θ e) (φ p))
    (hσ : ∀ x, ∃ s, ΓS s = sigPerm D x) {x₁ : L} (hx₁ : x₁ ≠ 0)
    (hl : ∃ s, ΓS s = lamPerm D x₁)
    (hQ : ∀ s w, Qt D (ΓS s w) = Qt D w) (hadd : ∀ s, IsAddPerm (ΓS s))
    (hinj : Function.Injective ΓS)
    (hSmax : ∀ T : Subgroup S, IsPGroup 2 T → Nat.card T ≤ Nat.card L)
    (S₁ S₂ : Subgroup S) [S₁.Normal] [S₂.Normal]
    (hA₁ : ∀ a ∈ A, ∀ e : ↥E, θ e ∈ S₁ →
      ∃ e' : ↥E, θ e' ∈ S₁ ∧ (e' : MulAut V) = a * e * a⁻¹)
    (hA₂ : ∀ a ∈ A, ∀ e : ↥E, θ e ∈ S₂ →
      ∃ e' : ↥E, θ e' ∈ S₂ ∧ (e' : MulAut V) = a * e * a⁻¹)
    (hidx : ∀ Ā' : Subgroup (Equiv.Perm (Wd F L)), (∀ a ∈ Ā', IsAddPerm a) →
      (∀ a ∈ Ā', a * a = 1) → (∀ a ∈ Ā', ∀ g ∈ ΓS.range, a * g * a⁻¹ ∈ ΓS.range) →
      (∀ a ∈ Ā', ∀ g ∈ S₁.map ΓS, a * g * a⁻¹ ∈ S₁.map ΓS) →
      (∀ a ∈ Ā', ∀ g ∈ S₂.map ΓS, a * g * a⁻¹ ∈ S₂.map ΓS) →
      (∀ a ∈ Ā', ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') →
      Nat.card Ā' ≤ 2 * Nat.card ↥(Ā' ⊓ Subgroup.centralizer
        (S0 D : Set (Equiv.Perm (Wd F L))))) :
    ⁅E, A⁆ = ⊥ := by
  classical
  have hEstab : E ≤ stabP P := le_stabP_of_invariant P hPE
  have hAstab : A ≤ stabP P := le_stabP_of_invariant P hPA
  let rS : stabP P →* Equiv.Perm (Wd F L) := resHom P φ
  have hrS : ∀ (g : MulAut V) (hg : g ∈ stabP P) (p : P),
      rS ⟨g, hg⟩ (φ p) = φ ⟨g p, (hg _ p.2).1⟩ := fun g hg p => resPerm_apply P φ g hg p
  have hrE : ∀ e : ↥E, rS ⟨e, hEstab e.2⟩ = ΓS (θ e) := by
    intro e
    ext w : 1
    obtain ⟨p, rfl⟩ := φ.surjective w
    rw [hrS, hequiv e p]
  have hAEstab : ∀ (a : ↥A) (e : ↥E), (⟨a, hAstab a.2⟩ : stabP P) * ⟨e, hEstab e.2⟩ *
      (⟨a, hAstab a.2⟩ : stabP P)⁻¹ =
        ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hEstab (hAE a a.2 e e.2)⟩ := fun a e =>
    Subtype.ext rfl
  have hconjE : ∀ (a : ↥A) (e : ↥E), rS ⟨a, hAstab a.2⟩ * ΓS (θ e) * (rS ⟨a, hAstab a.2⟩)⁻¹ =
      ΓS (θ ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hAE a a.2 e e.2⟩) := by
    intro a e
    have h1 := hrE ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hAE a a.2 e e.2⟩
    rw [← hrE e, ← map_inv, ← map_mul, ← map_mul, hAEstab]
    exact h1
  obtain ⟨rA, hrAdef⟩ : ∃ rA : A →* Equiv.Perm (Wd F L),
      rA = (resHom P φ).comp (Subgroup.inclusion hAstab) := ⟨_, rfl⟩
  have hrA : ∀ a : ↥A, rA a = rS ⟨a, hAstab a.2⟩ := fun a => by rw [hrAdef]; rfl
  have hΓσ : ∀ x, sigPerm D x ∈ ΓS.range := fun x => by
    obtain ⟨s, hs⟩ := hσ x
    exact ⟨s, hs⟩
  have hΓl : lamPerm D x₁ ∈ ΓS.range := by
    obtain ⟨s, hs⟩ := hl
    exact ⟨s, hs⟩
  have hΓQ : ∀ g ∈ ΓS.range, ∀ w, Qt D (g w) = Qt D w := by
    rintro _ ⟨s, rfl⟩ w
    exact hQ s w
  have hΓadd : ∀ g ∈ ΓS.range, IsAddPerm g := by
    rintro _ ⟨s, rfl⟩
    exact hadd s
  have hΓmax : ∀ T : Subgroup (Equiv.Perm (Wd F L)), T ≤ ΓS.range → IsPGroup 2 T →
      Nat.card T ≤ Nat.card L := by
    intro T hT hT2
    have hT' : IsPGroup 2 (T.comap ΓS) := fun x => by
      obtain ⟨k, hk⟩ := hT2 ⟨ΓS x, x.2⟩
      refine ⟨k, Subtype.ext (hinj ?_)⟩
      have := congrArg Subtype.val hk
      simpa [map_pow] using this
    have hcard : Nat.card (T.comap ΓS) = Nat.card T := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : T.comap ΓS => (⟨ΓS x, x.2⟩ : T)) ⟨?_, ?_⟩)
      · intro x y hxy
        exact Subtype.ext (hinj (congrArg Subtype.val hxy))
      · rintro ⟨g, hg⟩
        obtain ⟨s, rfl⟩ := hT hg
        exact ⟨⟨s, hg⟩, rfl⟩
    rw [← hcard]
    exact hSmax _ hT'
  have hΓ₁ : ∀ h ∈ ΓS.range, ∀ g ∈ S₁.map ΓS, h * g * h⁻¹ ∈ S₁.map ΓS := by
    rintro _ ⟨t, rfl⟩ _ ⟨s, hs, rfl⟩
    exact ⟨t * s * t⁻¹, Subgroup.Normal.conj_mem ‹S₁.Normal› s hs t, by simp⟩
  have hΓ₂ : ∀ h ∈ ΓS.range, ∀ g ∈ S₂.map ΓS, h * g * h⁻¹ ∈ S₂.map ΓS := by
    rintro _ ⟨t, rfl⟩ _ ⟨s, hs, rfl⟩
    exact ⟨t * s * t⁻¹, Subgroup.Normal.conj_mem ‹S₂.Normal› s hs t, by simp⟩
  have hadd' : ∀ a ∈ rA.range, IsAddPerm a := by
    rintro _ ⟨a, rfl⟩
    rw [hrA]
    exact resPerm_isAdd P φ hφ a (hAstab a.2)
  have hsq' : ∀ a ∈ rA.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have h2 : (a : MulAut V) * a = 1 := by
      have := hoff.2.2.1.2 a.1 a.2
      rwa [sq] at this
    have : a * a = 1 := Subtype.ext h2
    rw [this, map_one]
  have hnormΓ : ∀ a ∈ rA.range, ∀ g ∈ ΓS.range, a * g * a⁻¹ ∈ ΓS.range := by
    rintro _ ⟨a, rfl⟩ _ ⟨s, rfl⟩
    obtain ⟨e, rfl⟩ := θ.surjective s
    rw [hrA, hconjE a e]
    exact ⟨_, rfl⟩
  have hnorm₁ : ∀ a ∈ rA.range, ∀ g ∈ S₁.map ΓS, a * g * a⁻¹ ∈ S₁.map ΓS := by
    rintro _ ⟨a, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨e, rfl⟩ := θ.surjective s
    obtain ⟨e', he'S, he'⟩ := hA₁ a a.2 e hs
    refine ⟨θ e', he'S, ?_⟩
    rw [hrA, hconjE a e]
    have : e' = ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hAE a a.2 e e.2⟩ := Subtype.ext he'
    rw [this]
  have hnorm₂ : ∀ a ∈ rA.range, ∀ g ∈ S₂.map ΓS, a * g * a⁻¹ ∈ S₂.map ΓS := by
    rintro _ ⟨a, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨e, rfl⟩ := θ.surjective s
    obtain ⟨e', he'S, he'⟩ := hA₂ a a.2 e hs
    refine ⟨θ e', he'S, ?_⟩
    rw [hrA, hconjE a e]
    have : e' = ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hAE a a.2 e e.2⟩ := Subtype.ext he'
    rw [this]
  have hoff' : Nat.card (Wd F L) ≤ Nat.card rA.range * Nat.card (Fix rA.range) := by
    rw [hrAdef]
    exact offender_to_flag P φ hoff hAstab
  have hbot : rA.range = ⊥ :=
    flag_main D hF (Γ := ΓS.range) (Γ₁ := S₁.map ΓS) (Γ₂ := S₂.map ΓS) hΓσ hx₁ hΓl hΓQ hΓadd
      hΓmax hΓ₁ hΓ₂ hadd' hsq' hnormΓ hnorm₁ hnorm₂ hidx hoff'
  have hrA1 : ∀ a : ↥A, rA a = 1 := fun a => Subgroup.mem_bot.mp (hbot ▸ ⟨a, rfl⟩)
  have hcomm : ∀ (e : ↥E) (a : ↥A), (a : MulAut V) * e * (a : MulAut V)⁻¹ = e := by
    intro e a
    have h1 := hconjE a e
    rw [← hrA a, hrA1 a, one_mul, inv_one, mul_one] at h1
    have h2 : θ ⟨(a : MulAut V) * e * (a : MulAut V)⁻¹, hAE a a.2 e e.2⟩ = θ e :=
      hinj h1.symm
    exact congrArg Subtype.val (θ.injective h2)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro e he a ha
  rw [Subgroup.mem_bot]
  have h1 := hcomm ⟨e, he⟩ ⟨a, ha⟩
  have h2 : a * e = e * a := by
    calc a * e = a * e * a⁻¹ * a := by group
      _ = e * a := by rw [h1]
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact h2.symm

end Glue

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
