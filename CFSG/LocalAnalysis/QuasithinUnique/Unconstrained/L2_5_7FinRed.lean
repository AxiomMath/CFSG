module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt

public section

namespace CFSG.QuasithinUnique.Fin257

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.LieType.BorelTits

@[expose] def CoverElem (M : Type) [Group M] (R : Subgroup M) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → ∀ η : X →* M, Function.Surjective η →
    (∀ z, η z = 1 → ∀ y, z * y = y * z) → IsPGroup 2 η.ker → (∀ z ∈ η.ker, z ^ 2 = 1) →
    IsElemAbelian 2 (R.comap η)

structure ModelPkg (M : Type) [Group M] (U R₁ R₂ : Subgroup M) : Prop where
  data : ModelData M U R₁ R₂
  cov₁ : CoverElem M R₁
  cov₂ : CoverElem M R₂

theorem ModelPkg.symm {M : Type} [Group M] {U R₁ R₂ : Subgroup M} (h : ModelPkg M U R₁ R₂) :
    ModelPkg M U R₂ R₁ where
  data := h.data.symm
  cov₁ := h.cov₂
  cov₂ := h.cov₁

theorem isElemAbelian_of_comap {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} {R : Subgroup M} (h : IsElemAbelian 2 (R.comap π)) :
    IsElemAbelian 2 (pre π R) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨hxK, hxR⟩ := mem_pre.mp hx
    obtain ⟨hyK, hyR⟩ := mem_pre.mp hy
    have := h.1.is_comm.comm (⟨⟨x, hxK⟩, hxR⟩ : ↥(R.comap π)) ⟨⟨y, hyK⟩, hyR⟩
    exact congrArg (fun t : ↥(R.comap π) => ((t : ↥K) : G)) this
  · obtain ⟨hxK, hxR⟩ := mem_pre.mp hx
    have := h.2 ⟨x, hxK⟩ hxR
    exact congrArg (fun t : ↥K => (t : G)) this

theorem geom_of_red {G : Type} [Group G] [Finite G] {K P K₁ K₂ V V' : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    {π : ↥K →* M} (hred : Red257 K P K₁ K₂ V V' π U R₁ R₂) (hpkg : ModelPkg M U R₁ R₂)
    (hZ : IsElemAbelian 2 (K ⊓ Subgroup.centralizer (K : Set G))) :
    RankTwoGeometry257 P V V' := by
  have hsq : ∀ z ∈ π.ker, z ^ 2 = 1 := by
    intro z hz
    have hzc : (z : G) ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
      refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg (fun t : ↥K => (t : G))
        (hred.ker_central z (MonoidHom.mem_ker.mp hz) ⟨h, hh⟩).symm
    have := hZ.2 (z : G) hzc
    exact Subtype.ext (by simpa using this)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hred.hV]
    exact isElemAbelian_of_comap
      (hpkg.cov₁ ↥K hq.1 π hred.surj hred.ker_central hred.ker_two hsq)
  · rw [hred.hP, ← hpkg.data.sup, hred.hV, hred.hV', pre_sup hred.surj]
  · rw [hred.hV, hred.hV']
    intro h
    exact hpkg.data.ne (pre_injective hred.surj h)
  · rw [hred.hV, hred.hV']
    intro hle
    apply hpkg.data.noncomm
    intro r₂ hr₂
    rw [Subgroup.mem_centralizer_iff]
    intro r₁ hr₁
    obtain ⟨a, rfl⟩ := hred.surj r₂
    obtain ⟨b, rfl⟩ := hred.surj r₁
    have ha : (a : G) ∈ pre π R₂ := mem_pre_of_mem a hr₂
    have hb : (b : G) ∈ pre π R₁ := mem_pre_of_mem b hr₁
    have := Subgroup.mem_centralizer_iff.mp (hle ha) (b : G) hb
    have h2 : b * a = a * b := Subtype.ext this
    rw [← map_mul, ← map_mul, h2]

theorem autOdd_of_red {G : Type} [Group G] [Finite G] {K P K₁ K₂ V V' : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hpair : IsParabolicPair257 K P K₁ K₂)
    {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    {π : ↥K →* M} (hred : Red257 K P K₁ K₂ V V' π U R₁ R₂) (hM : ModelData M U R₁ R₂) :
    ∀ g ∈ Subgroup.normalizer (K : Set G), g ∈ Subgroup.normalizer (P : Set G) →
      Odd (orderOf g) → (∀ s ∈ P, s⁻¹ * g⁻¹ * s * g ∈ V ⊓ V') →
        g ∈ Subgroup.centralizer (K : Set G) := by
  intro g hgK _ hodd hhyp
  have hgK' : ∀ x ∈ K, g⁻¹ * x * g ∈ K := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgK) x).mp hx
    simpa using this
  have hgK'' : ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hgK x).mp hx
  let β : ↥K ≃* ↥K :=
    { toFun := fun x => ⟨g⁻¹ * x * g, hgK' x x.2⟩
      invFun := fun x => ⟨g * x * g⁻¹, hgK'' x x.2⟩
      left_inv := fun x => by apply Subtype.ext; simp [mul_assoc]
      right_inv := fun x => by apply Subtype.ext; simp [mul_assoc]
      map_mul' := fun x y => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hβx : ∀ x : ↥K, ((β x : ↥K) : G) = g⁻¹ * x * g := fun x => rfl
  have hcentral : ∀ (γ : ↥K ≃* ↥K) (x : ↥K), (∀ y, x * y = y * x) → ∀ y, γ x * y = y * γ x := by
    intro γ x hx y
    have := hx (γ.symm y)
    have h2 := congrArg γ this
    simpa using h2
  have hβker : π.ker.map β.toMonoidHom = π.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MonoidHom.mem_ker.mpr (hred.center_le _ (hcentral β x (hred.ker_central x
        (MonoidHom.mem_ker.mp hx))))
    · intro hy
      refine ⟨β.symm y, ?_, by simp⟩
      exact MonoidHom.mem_ker.mpr (hred.center_le _ (hcentral β.symm y (hred.ker_central y
        (MonoidHom.mem_ker.mp hy))))
  let ᾱ : MulAut M := inducedAut π hred.surj β hβker
  have hᾱ : ∀ x : ↥K, ᾱ (π x) = π (β x) := fun x => inducedAut_apply π hred.surj β hβker x
  have hαpow : ∀ (k : ℕ) (x : ↥K), (ᾱ ^ k) (π x) = π ((β ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hᾱ]
  have hβpow : ∀ (k : ℕ) (x : ↥K), (((β ^ k) x : ↥K) : G) = (g⁻¹) ^ k * x * g ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hβx, ih, pow_succ' g⁻¹ k, pow_succ g k]
      group
  have hαm : ᾱ ^ orderOf g = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hred.surj y
    rw [hαpow, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hβpow, pow_orderOf_eq_one, inv_pow, pow_orderOf_eq_one]
    simp
  have hU : ∀ u ∈ U, u⁻¹ * ᾱ u ∈ R₁ ⊓ R₂ := by
    intro u hu
    obtain ⟨x, rfl⟩ := hred.surj u
    have hxP : (x : G) ∈ P := by
      rw [hred.hP]
      exact mem_pre_of_mem x hu
    have h1 := hhyp x hxP
    rw [hred.hV, hred.hV', ← pre_inf, mem_pre] at h1
    obtain ⟨hK, h2⟩ := h1
    have e : (⟨(x : G)⁻¹ * g⁻¹ * x * g, hK⟩ : ↥K) = x⁻¹ * β x := by
      apply Subtype.ext
      simp [hβx, mul_assoc]
    rw [e, map_mul, map_inv, ← hᾱ] at h2
    exact h2
  have hsup : Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) = ⊤ := by
    have h := hpair.sup_eq
    rw [hred.hK₁, hred.hK₂, ← pre_sup hred.surj] at h
    have h' : pre π (Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M)) =
        pre π ⊤ := by
      rw [pre_top]
      exact h
    exact pre_injective hred.surj h'
  have hR₁2 : IsPGroup 2 R₁ := fun x => ⟨1, by
    have := hM.elem₁.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  have hR₂2 : IsPGroup 2 R₂ := fun x => ⟨1, by
    have := hM.elem₂.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  have hab₁ : ∀ x ∈ R₁, ∀ y ∈ R₁, x * y = y * x := fun x hx y hy => by
    have := hM.elem₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hab₂ : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x := fun x hx y hy => by
    have := hM.elem₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hα1 : ᾱ = 1 :=
    ao_model R₁ R₂ U hR₁2 hR₂2 hab₁ hab₂ hM.inter_le_comm hM.cent₁ hM.cent₂ hsup hM.le₁ hM.le₂
      ᾱ hodd hαm hU
  have hβπ : ∀ x : ↥K, π (β x) = π x := fun x => by
    rw [← hᾱ, hα1]
    rfl
  have hZcen : ∀ z ∈ pre π (⊥ : Subgroup M), ∀ x ∈ K, z * x = x * z := by
    intro z hz x hx
    obtain ⟨hzK, hz1⟩ := mem_pre.mp hz
    exact congrArg Subtype.val
      (hred.ker_central ⟨z, hzK⟩ (Subgroup.mem_bot.mp hz1) ⟨x, hx⟩)
  have hZab : ∀ z ∈ pre π (⊥ : Subgroup M), ∀ z' ∈ pre π (⊥ : Subgroup M), z * z' = z' * z :=
    fun z hz z' hz' => hZcen z hz z' (pre_le_K _ hz')
  have hgZ : ∀ x ∈ K, x⁻¹ * g⁻¹ * x * g ∈ pre π (⊥ : Subgroup M) := by
    intro x hx
    have hK : x⁻¹ * g⁻¹ * x * g ∈ K := by
      have := ((⟨x, hx⟩ : ↥K)⁻¹ * β ⟨x, hx⟩).2
      simpa [hβx, mul_assoc] using this
    refine mem_pre.mpr ⟨hK, ?_⟩
    have e : (⟨x⁻¹ * g⁻¹ * x * g, hK⟩ : ↥K) = (⟨x, hx⟩ : ↥K)⁻¹ * β ⟨x, hx⟩ := by
      apply Subtype.ext
      simp [hβx, mul_assoc]
    rw [e, map_mul, map_inv, hβπ, inv_mul_cancel]
    exact Subgroup.one_mem _
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  exact (centralizes_of_perfect K (pre π ⊥) hq.1.commutator_eq_top hZcen hZab g hgZ x hx).symm

theorem torus_of_red {G : Type} [Group G] [Finite G] {K P K₁ K₂ V V' : Subgroup G}
    {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    {π : ↥K →* M} (hred : Red257 K P K₁ K₂ V V' π U R₁ R₂) (hM : ModelData M U R₁ R₂) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ P₀ : Subgroup G, P₀ ≤ K ∧ IsElemAbelian p P₀ ∧
        Nat.card P₀ = p ^ 2) ∧
      ∃ h ∈ K ⊓ Subgroup.normalizer (P : Set G), (∃ k : ℕ, orderOf h = p ^ k) ∧
        ¬ ⁅V, V'⁆ ≤ Subgroup.centralizer ({h} : Set G) := by
  obtain ⟨p, hp, hp2, ⟨P₀b, hP₀e, hP₀c⟩, hb, hhn, ⟨k, hk⟩, hhc⟩ := hM.torus
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  refine ⟨p, hp, hp2, ?_, ?_⟩
  ·
    have hcop : Nat.Coprime 2 (Nat.card P₀b) := by
      rw [hP₀c]
      exact hcop2.pow_right 2
    obtain ⟨σ, hσ⟩ := Wielandt.exists_lift_of_surjective_isPGroup_ker_of_coprime π hred.surj
      hred.ker_two hcop P₀b.subtype
    have hσinj : Function.Injective σ := by
      intro a b hab
      have : π (σ a) = π (σ b) := congrArg π hab
      have h2 : (P₀b.subtype : ↥P₀b →* M) a = (P₀b.subtype : ↥P₀b →* M) b := by
        rw [← hσ]
        exact this
      exact Subtype.ext h2
    refine ⟨σ.range.map K.subtype, Subgroup.map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
    · refine isMulCommutative_iff_of_setLike.mpr ?_
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
      have := hP₀e.1.is_comm.comm a b
      have h2 := congrArg σ this
      rw [map_mul, map_mul] at h2
      exact congrArg (fun t : ↥K => (t : G)) h2
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      have := hP₀e.2 a a.2
      have h2 : (a : ↥P₀b) ^ p = 1 := Subtype.ext this
      have h3 := congrArg σ h2
      rw [map_pow, map_one] at h3
      exact congrArg (fun t : ↥K => (t : G)) h3
    · rw [Subgroup.card_map_of_injective K.subtype_injective,
        Nat.card_congr (MonoidHom.ofInjective hσinj).symm.toEquiv, hP₀c]
  · have hcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers hb)) := by
      rw [Nat.card_zpowers, hk]
      exact hcop2.pow_right k
    obtain ⟨σ, hσ⟩ := Wielandt.exists_lift_of_surjective_isPGroup_ker_of_coprime π hred.surj
      hred.ker_two hcop (Subgroup.zpowers hb).subtype
    set x : ↥K := σ ⟨hb, Subgroup.mem_zpowers hb⟩ with hx
    have hπx : π x = hb := by
      have := congrArg (fun f : ↥(Subgroup.zpowers hb) →* M => f ⟨hb, Subgroup.mem_zpowers hb⟩) hσ
      simpa using this
    refine ⟨(x : G), ?_, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      have : (x : G) ∈ pre π (Subgroup.normalizer (U : Set M)) :=
        mem_pre_of_mem x (by rw [hπx]; exact hhn)
      rw [pre_normalizer hred.surj, ← hred.hP] at this
      exact (Subgroup.mem_inf.mp this).2
    · have h1 : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
      have h2 : orderOf x ∣ orderOf (⟨hb, Subgroup.mem_zpowers hb⟩ : ↥(Subgroup.zpowers hb)) :=
        orderOf_map_dvd σ _
      have h3 : orderOf (⟨hb, Subgroup.mem_zpowers hb⟩ : ↥(Subgroup.zpowers hb)) = orderOf hb :=
        Subgroup.orderOf_mk _ _
      rw [h3, hk] at h2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h2
      exact ⟨j, by rw [h1, hj]⟩
    · intro hle
      apply hhc
      rw [Subgroup.commutator_le]
      intro a ha b hb'
      obtain ⟨xa, rfl⟩ := hred.surj a
      obtain ⟨xb, rfl⟩ := hred.surj b
      have hVa : (xa : G) ∈ V := by
        rw [hred.hV]
        exact mem_pre_of_mem xa ha
      have hVb : (xb : G) ∈ V' := by
        rw [hred.hV']
        exact mem_pre_of_mem xb hb'
      have hc := hle (Subgroup.commutator_mem_commutator hVa hVb)
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      have h2 : ⁅xa, xb⁆ * x = x * ⁅xa, xb⁆ :=
        Subtype.ext (by simpa [commutatorElement_def] using hc)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg π h2
      rw [map_mul, map_mul, hπx, map_commutatorElement] at this
      exact this

end CFSG.QuasithinUnique.Fin257
