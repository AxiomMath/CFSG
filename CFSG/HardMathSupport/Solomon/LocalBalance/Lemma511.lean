module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

namespace Lemma511Ns

open scoped commutatorElement

@[expose] def HasOrderThreeLift (Y : Type*) [Group Y] (y : Y) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (θ : Y ≃* StatedProj (StatedSL 3 K)),
      Nat.card K % 3 = 1 ∧
        ∃ ŷ : ↥(StatedSL 3 K), orderOf ŷ = 3 ∧ θ y = QuotientGroup.mk ŷ) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ) (θ : Y ≃* StatedProj (StatedSU 3 q K)),
      Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
        ∃ ŷ : ↥(StatedSU 3 q K), orderOf ŷ = 3 ∧ θ y = QuotientGroup.mk ŷ)

@[expose] def Input30_2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (y : Y), y ≠ 1 → HasOrderThreeLift Y y →
    ∃ F : Subgroup Y, y ∈ F ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      (∃ f : QuaternionGroup 2 →* autizer (⊤ : Subgroup Y) F, Function.Injective f) ∧
      ∀ u ∈ F, ∀ v ∈ F, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (F : Set Y), g * u * g⁻¹ = v

@[expose] def Input20_27_2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ → IsExtremalType Y → ¬ IsLThreeFour Y →
    ∀ B : Subgroup (MulAut Y), IsPGroup 3 B → B ≠ ⊥ →
      ∃ S : Subgroup Y, S ≠ ⊥ ∧ Nat.Coprime 3 (Nat.card S) ∧
        ∀ β ∈ B, S.map β.toMonoidHom = S

@[expose] def InputL3Center : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsExtremalType Y → Subgroup.center Y = ⊥

@[expose] def InputL3FieldInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsExtremalType Y →
    ∀ y : Y, IsFieldAutThree (MulAut.conj y) → MulAut.conj y = 1

@[expose] def Gap_JStructure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L → IsExtremalType (barOf 3 L) →
      ∀ A : Subgroup G, IsEkIn 3 2 B A → b ∈ A → (∀ a ∈ A, InducesFieldAut 3 L a) →
        3 ∣ Nat.card ↥(GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))) ∧
        ∀ (y : G) (hy : y ∈ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))), y ∈ B → y ≠ 1 →
          HasOrderThreeLift (barOf 3 (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))))
            (QuotientGroup.mk (⟨y, hy⟩ : ↥(GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))))

@[expose] def Gap_KxType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L → IsExtremalType (barOf 3 L) →
      ∀ A F : Subgroup G, IsEkIn 3 2 B A → b ∈ A → (∀ a ∈ A, InducesFieldAut 3 L a) →
        IsElemAbelian 3 F → Nat.card F = 9 → F ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) →
        ∀ x ∈ B, x ∈ F ⊔ A → x ≠ 1 → InducesFieldAut 3 L x →
          ¬ IsSLThreeEps (barOf 3 (pumpUp L x))

section AutCongr

variable {M : Type*} [Group M]

@[expose] def autAct (X T : Subgroup M) : ↥(X ⊓ Subgroup.normalizer (T : Set M)) →* MulAut ↥T :=
  T.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_right : X ⊓ Subgroup.normalizer (T : Set M) ≤ Subgroup.normalizer (T : Set M)))

theorem autAct_coe (X T : Subgroup M) (g : ↥(X ⊓ Subgroup.normalizer (T : Set M))) (t : ↥T) :
    ((autAct X T g t : ↥T) : M) = (g : M) * t * (g : M)⁻¹ := rfl

theorem ker_autAct (X T : Subgroup M) :
    (autAct X T).ker = (X ⊓ Subgroup.centralizer (T : Set M)).subgroupOf (X ⊓ Subgroup.normalizer (T : Set M)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨g.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := congrArg (fun α : MulAut ↥T => ((α ⟨t, ht⟩ : ↥T) : M)) h
    simp only [autAct_coe, MulAut.one_apply] at this
    calc t * (g : M) = ((g : M) * t * (g : M)⁻¹) * g := by rw [this]
      _ = (g : M) * t := by group
  · rintro ⟨-, h⟩
    ext t
    rw [autAct_coe]
    have := Subgroup.mem_centralizer_iff.1 h t t.2
    show (g : M) * t * (g : M)⁻¹ = t
    calc (g : M) * t * (g : M)⁻¹ = (t * g) * (g : M)⁻¹ := by rw [← this]
      _ = t := by group

noncomputable def autizerEquivRange (X T : Subgroup M) : autizer X T ≃* (autAct X T).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_autAct X T).symm).trans
    (QuotientGroup.quotientKerEquivRange (autAct X T))

theorem autizer_congr {M' : Type*} [Group M'] {X T : Subgroup M} {X' T' : Subgroup M'}
    (e : ↥T ≃* ↥T')
    (h1 : ∀ g : ↥(X ⊓ Subgroup.normalizer (T : Set M)), ∃ g' : ↥(X' ⊓ Subgroup.normalizer (T' : Set M')),
      ∀ t : ↥T, ((e (autAct X T g t) : ↥T') : M') = (g' : M') * ((e t : ↥T') : M') * (g' : M')⁻¹)
    (h2 : ∀ g' : ↥(X' ⊓ Subgroup.normalizer (T' : Set M')), ∃ g : ↥(X ⊓ Subgroup.normalizer (T : Set M)),
      ∀ t : ↥T, ((e (autAct X T g t) : ↥T') : M') = (g' : M') * ((e t : ↥T') : M') * (g' : M')⁻¹) :
    Nonempty (autizer X T ≃* autizer X' T') := by
  have key : ∀ (g : ↥(X ⊓ Subgroup.normalizer (T : Set M)))
      (g' : ↥(X' ⊓ Subgroup.normalizer (T' : Set M'))),
      (∀ t : ↥T, ((e (autAct X T g t) : ↥T') : M') = (g' : M') * ((e t : ↥T') : M') * (g' : M')⁻¹) →
      autAct X' T' g' = MulAut.congr e (autAct X T g) := by
    intro g g' h
    ext t'
    rw [MulAut.congr_apply]
    have := h (e.symm t')
    rw [MulEquiv.apply_symm_apply] at this
    rw [autAct_coe]
    exact this.symm
  have hrange : (autAct X T).range.map (MulAut.congr e).toMonoidHom = (autAct X' T').range := by
    ext α
    simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨β, ⟨g, rfl⟩, rfl⟩
      obtain ⟨g', hg'⟩ := h1 g
      exact ⟨g', key g g' hg'⟩
    · rintro ⟨g', rfl⟩
      obtain ⟨g, hg⟩ := h2 g'
      exact ⟨_, ⟨g, rfl⟩, (key g g' hg).symm⟩
  exact ⟨(autizerEquivRange X T).trans
    (((MulEquiv.subgroupMap (MulAut.congr e) _).trans (MulEquiv.subgroupCongr hrange)).trans
      (autizerEquivRange X' T').symm)⟩

end AutCongr

section Syl

variable {H : Type*} [Group H] [Finite H]

theorem l2_eq_one_of_coprime {N : Subgroup H} (hN : Nat.Coprime 3 (Nat.card N)) {u : H}
    (hu : u ∈ N) {k : ℕ} (hk : u ^ (3 ^ k) = 1) : u = 1 := by
  let w : ↥N := ⟨u, hu⟩
  have hw : w ^ (3 ^ k) = 1 := Subtype.ext hk
  have hd1 : orderOf w ∣ Nat.card N := orderOf_dvd_natCard w
  have hd2 : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hw
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) := Nat.Coprime.pow_left k hN
  have h3 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1
  have h4 : w = 1 := orderOf_eq_one_iff.1 h3
  exact congrArg Subtype.val h4

theorem l2_sylow (N : Subgroup H) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    (Fb : Subgroup (H ⧸ N)) (hFel : IsElemAbelian 3 Fb) (hFc : Nat.card Fb = 9)
    (y₀ : H) (hy3 : y₀ ^ 3 = 1) (hy : (y₀ : H ⧸ N) ∈ Fb) :
    ∃ S : Subgroup H, y₀ ∈ S ∧ IsElemAbelian 3 S ∧ Nat.card S = 9 ∧
      Set.InjOn (QuotientGroup.mk : H → H ⧸ N) S ∧ (∀ u ∈ S, (u : H ⧸ N) ∈ Fb) ∧
      (∀ f ∈ Fb, ∃ u ∈ S, (u : H ⧸ N) = f) ∧
      (∀ n : H ⧸ N, n ∈ Subgroup.normalizer (Fb : Set (H ⧸ N)) →
        ∃ m ∈ Subgroup.normalizer (S : Set H), ∀ u ∈ S,
          ((m * u * m⁻¹ : H) : H ⧸ N) = n * (u : H ⧸ N) * n⁻¹) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let P : Subgroup H := Fb.comap π
  have hyP : y₀ ∈ P := hy
  let y' : ↥P := ⟨y₀, hyP⟩
  have hZ : IsPGroup 3 (Subgroup.zpowers y') := by
    intro z
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).1 z.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : y' ^ 3 = 1 := Subtype.ext hy3
    rw [this, one_zpow]; rfl
  obtain ⟨Sy, hZSy⟩ := hZ.exists_le_sylow
  have hSyp : IsPGroup 3 (Sy : Subgroup ↥P) := Sy.isPGroup'
  let ρ : ↥P →* ↥Fb := (π.comp P.subtype).codRestrict Fb (fun x => x.2)
  have hρc : ∀ x : ↥P, ((ρ x : ↥Fb) : H ⧸ N) = (x : H ⧸ N) := fun x => rfl
  have hρ : Function.Surjective ρ := by
    intro f
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (f : H ⧸ N)
    exact ⟨⟨h, by show (h : H ⧸ N) ∈ Fb; rw [hh]; exact f.2⟩, Subtype.ext hh⟩
  have hinj : ∀ x ∈ (Sy : Subgroup ↥P), ρ x = 1 → x = 1 := by
    intro x hx hρx
    have hxN : (x : H) ∈ N := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hρx)
    obtain ⟨k, hk⟩ := hSyp ⟨x, hx⟩
    have : (x : H) ^ (3 ^ k) = 1 := by
      have := congrArg (fun z : ↥(Sy : Subgroup ↥P) => ((z : ↥P) : H)) hk
      simpa using this
    exact Subtype.ext (l2_eq_one_of_coprime hN hxN this)
  have hinj' : Function.Injective (ρ.comp (Sy : Subgroup ↥P).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (ρ.comp (Sy : Subgroup ↥P).subtype).range = (Sy : Subgroup ↥P).map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardmap : Nat.card ↥((Sy : Subgroup ↥P).map ρ) = 9 := by
    have := (Sy.mapSurjective hρ).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective, hFc] at this
    rw [this]
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hmaptop : (Sy : Subgroup ↥P).map ρ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardmap, hFc]
  have hcardSy : Nat.card (Sy : Subgroup ↥P) = 9 := by
    rw [← hcardmap, ← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
  let S : Subgroup H := (Sy : Subgroup ↥P).map P.subtype
  have hmemS : ∀ u, u ∈ S ↔ ∃ x ∈ (Sy : Subgroup ↥P), (x : H) = u := by
    intro u; exact Subgroup.mem_map
  have hSP : ∀ u ∈ S, (u : H ⧸ N) ∈ Fb := by
    intro u hu
    obtain ⟨x, -, rfl⟩ := (hmemS u).1 hu
    exact x.2
  have hSinj : Set.InjOn (QuotientGroup.mk : H → H ⧸ N) S := by
    intro u hu v hv huv
    obtain ⟨x₁, hx₁, rfl⟩ := (hmemS u).1 hu
    obtain ⟨x₂, hx₂, rfl⟩ := (hmemS v).1 hv
    have h1 : ρ x₁ = ρ x₂ := Subtype.ext huv
    have h2 : x₁⁻¹ * x₂ = 1 := hinj _ ((Sy : Subgroup ↥P).mul_mem ((Sy : Subgroup ↥P).inv_mem hx₁) hx₂)
      (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    have : x₁ = x₂ := inv_mul_eq_one.1 h2
    rw [this]
  have hScard : Nat.card S = 9 := by
    rw [← hcardSy]
    exact Subgroup.card_map_of_injective P.subtype_injective
  have hSel : IsElemAbelian 3 S := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have ha := hSP a a.2
      have hb := hSP b b.2
      have hc := elemAbelian_comm hFel ha hb
      have hmem1 : (a : H) * b ∈ S := S.mul_mem a.2 b.2
      have hmem2 : (b : H) * a ∈ S := S.mul_mem b.2 a.2
      exact hSinj hmem1 hmem2 (by
        show (QuotientGroup.mk ((a : H) * b) : H ⧸ N) = QuotientGroup.mk ((b : H) * a)
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc)
    · have hx' := hSP x hx
      have h3 := hFel.2 _ hx'
      have hmem : x ^ 3 ∈ S := S.pow_mem hx 3
      refine hSinj hmem S.one_mem ?_
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]
      exact h3
  have hSont : ∀ f ∈ Fb, ∃ u ∈ S, (u : H ⧸ N) = f := by
    intro f hf
    have : (⟨f, hf⟩ : ↥Fb) ∈ (Sy : Subgroup ↥P).map ρ := by rw [hmaptop]; trivial
    obtain ⟨x, hx, hxf⟩ := this
    exact ⟨(x : H), (hmemS _).2 ⟨x, hx, rfl⟩, congrArg Subtype.val hxf⟩
  have hy₀S : y₀ ∈ S := (hmemS _).2 ⟨y', hZSy (Subgroup.mem_zpowers y'), rfl⟩
  refine ⟨S, hy₀S, hSel, hScard, hSinj, hSP, hSont, ?_⟩
  intro nb hnb
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective nb
  have hnP : n ∈ Subgroup.normalizer (P : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 hnb (x : H ⧸ N)
    show (x : H ⧸ N) ∈ Fb ↔ ((n * x * n⁻¹ : H) : H ⧸ N) ∈ Fb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact this
  let φ : MulAut ↥P := P.normalizerMonoidHom ⟨n, hnP⟩
  have hφc : ∀ x : ↥P, ((φ x : ↥P) : H) = n * x * n⁻¹ := fun x => rfl
  let Sy₁ : Sylow 3 ↥P := Sylow.ofCard ((Sy : Subgroup ↥P).map φ.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]; exact Sy.card_eq_multiplicity)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P Sy₁ Sy
  have hconj : ∀ y : ↥P, y ∈ (Sy : Subgroup ↥P) ↔ ∃ z ∈ (Sy₁ : Subgroup ↥P), g * z * g⁻¹ = y := by
    intro y
    have h1 : y ∈ ((g • Sy₁ : Sylow 3 ↥P) : Subgroup ↥P) ↔ y ∈ (Sy : Subgroup ↥P) := by rw [hg]
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply]
  refine ⟨(g : H) * n, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      obtain ⟨x, hx, rfl⟩ := (hmemS u).1 hu
      have : g * φ x * g⁻¹ ∈ (Sy : Subgroup ↥P) := (hconj _).2 ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
      refine (hmemS _).2 ⟨_, this, ?_⟩
      show ((g * φ x * g⁻¹ : ↥P) : H) = (g : H) * n * (x : H) * ((g : H) * n)⁻¹
      have : ((g * φ x * g⁻¹ : ↥P) : H) = (g : H) * (n * (x : H) * n⁻¹) * (g : H)⁻¹ := rfl
      rw [this]; group
    · intro hu
      obtain ⟨y, hy, hyu⟩ := (hmemS _).1 hu
      obtain ⟨z, hz, rfl⟩ := (hconj y).1 hy
      obtain ⟨x, hx, rfl⟩ := hz
      have e : (g : H) * n * (x : H) * ((g : H) * n)⁻¹ = (g : H) * n * u * ((g : H) * n)⁻¹ := by
        rw [← hyu]
        have : ((g * φ.toMonoidHom x * g⁻¹ : ↥P) : H) = (g : H) * (n * (x : H) * n⁻¹) * (g : H)⁻¹ := rfl
        rw [this]; group
      have hxu : (x : H) = u := mul_left_cancel (mul_right_cancel e)
      exact (hmemS u).2 ⟨x, hx, hxu⟩
  · intro u hu
    have hgP : ((g : H) : H ⧸ N) ∈ Fb := g.2
    have hw : (n : H ⧸ N) * (u : H ⧸ N) * (n : H ⧸ N)⁻¹ ∈ Fb :=
      (Subgroup.mem_normalizer_iff.1 hnb (u : H ⧸ N)).1 (hSP u hu)
    have hc := elemAbelian_comm hFel hgP hw
    have e : ((g : H) * n * u * ((g : H) * n)⁻¹ : H) = (g : H) * (n * u * n⁻¹) * (g : H)⁻¹ := by
      group
    rw [e]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc]; group

end Syl

section Elem

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_inf_ne_one_of_isSCp {B J : Subgroup G}
    (hB : IsSCp 3 ⊤ B) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (h3 : 3 ∣ Nat.card J) :
    ∃ y ∈ B ⊓ J, y ≠ 1 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hB.2.1
  have hPB : IsPGroup 3 B := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hBel.2 x x.2)⟩
  let _ : MulAction B J :=
    MulAction.compHom J ((Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBJ))
  have hsmul : ∀ (g : B) (x : J), ((g • x : J) : G) = (g : G) * x * (g : G)⁻¹ := fun g x => rfl
  have hmod := hPB.card_modEq_card_fixedPoints J
  have h3fix : 3 ∣ Nat.card (MulAction.fixedPoints B J) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h3))
  let S : Subgroup G := J ⊓ Subgroup.centralizer (B : Set G)
  have hcard : Nat.card (MulAction.fixedPoints B J) = Nat.card S := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · show (x.1.1 : G) ∈ Subgroup.centralizer (B : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 : ((⟨g, hg⟩ : B) • x.1 : J) = x.1 := x.2 ⟨g, hg⟩
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      show g * x.1.1 = x.1.1 * g
      calc g * x.1.1 = (g * x.1.1 * g⁻¹) * g := by group
        _ = x.1.1 * g := by rw [show (g * x.1.1 * g⁻¹ : G) = x.1.1 from h2]
    · intro g
      apply Subtype.ext
      rw [hsmul]
      have := Subgroup.mem_centralizer_iff.1 y.2.2 g g.2
      show (g : G) * y.1 * (g : G)⁻¹ = y.1
      rw [this]; group
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 (hcard ▸ h3fix)
  have hy3 : ((y : G)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    norm_num at hy
  have hel : IsElemAbelian 3 (B ⊔ Subgroup.zpowers (y : G)) := by
    refine isElemAbelian_sup_of_commute hBel ⟨inferInstance, ?_⟩ ?_
    · intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    · intro g hg u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have := Subgroup.mem_centralizer_iff.1 y.2.2 g hg
      exact (Commute.zpow_right (show Commute g (y : G) from this) k).eq.symm
  have hEB := hB.2.2 _ le_top hel le_sup_left
  refine ⟨y, ⟨?_, y.2.1⟩, hy1⟩
  rw [← hEB]
  exact (le_sup_right : Subgroup.zpowers (y : G) ≤ _) (Subgroup.mem_zpowers _)

theorem exists_lift_of_quotient (J : Subgroup G) (y : G) (hyJ : y ∈ J) (hy3 : y ^ 3 = 1)
    (_hy1 : y ≠ 1) (Fb : Subgroup (barOf 3 J))
    (hy : (QuotientGroup.mk (⟨y, hyJ⟩ : ↥J) : barOf 3 J) ∈ Fb)
    (hFel : IsElemAbelian 3 Fb) (hFc : Nat.card Fb = 9)
    (hQ : ∃ f : QuaternionGroup 2 →* autizer (⊤ : Subgroup (barOf 3 J)) Fb, Function.Injective f)
    (hT : ∀ u ∈ Fb, ∀ v ∈ Fb, u ≠ 1 → v ≠ 1 →
      ∃ g ∈ (⊤ : Subgroup (barOf 3 J)) ⊓ Subgroup.normalizer (Fb : Set (barOf 3 J)), g * u * g⁻¹ = v) :
    ∃ F : Subgroup G, F ≤ J ∧ y ∈ F ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      (∃ f : QuaternionGroup 2 →* autizer J F, Function.Injective f) ∧
      ∀ u ∈ F, ∀ v ∈ F, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ J ⊓ Subgroup.normalizer (F : Set G), g * u * g⁻¹ = v := by
  have hN := coprime_card_gLAPPrimeCore_aux 3 ↥J
  obtain ⟨S, hy₀S, hSel, hScard, hSinj, hSP, hSont, hact⟩ :=
    l2_sylow (GLAPPrimeCore 3 ↥J) hN Fb hFel hFc ⟨y, hyJ⟩ (Subtype.ext hy3) hy
  let F : Subgroup G := S.map J.subtype
  have hmemF : ∀ v, v ∈ F ↔ ∃ u ∈ S, ((u : ↥J) : G) = v := fun v => Subgroup.mem_map
  have hFJ : F ≤ J := Subgroup.map_subtype_le S
  have hconjS : ∀ h : ↥J, (h : G) ∈ Subgroup.normalizer (F : Set G) → ∀ u ∈ S, h * u * h⁻¹ ∈ S := by
    intro h hh u hu
    have hu' : ((u : ↥J) : G) ∈ F := (hmemF _).2 ⟨u, hu, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hh _).1 hu'
    obtain ⟨s, hs, hsu⟩ := (hmemF _).1 this
    have : s = h * u * h⁻¹ := Subtype.ext hsu
    rw [← this]; exact hs
  have hmF : ∀ m : ↥J, m ∈ Subgroup.normalizer (S : Set ↥J) → (m : G) ∈ Subgroup.normalizer (F : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (hmemF v).1 hv
      refine (hmemF _).2 ⟨m * u * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm u).1 hu, rfl⟩
    · intro hv
      obtain ⟨s, hs, hsv⟩ := (hmemF _).1 hv
      have hvJ : v ∈ J := by
        have h1 : v = ((m⁻¹ * s * m : ↥J) : G) := by
          show v = (m : G)⁻¹ * (s : G) * (m : G)
          rw [hsv]; group
        rw [h1]; exact (m⁻¹ * s * m).2
      have hw : m⁻¹ * s * m ∈ S := by
        have := (Subgroup.mem_normalizer_iff.1 hm (m⁻¹ * s * m)).2
        have h2 : m * (m⁻¹ * s * m) * m⁻¹ = s := by group
        rw [h2] at this
        exact this hs
      refine (hmemF v).2 ⟨m⁻¹ * s * m, hw, ?_⟩
      have : (s : G) = (m : G) * v * (m : G)⁻¹ := hsv
      rw [show (((m⁻¹ * s * m : ↥J)) : G) = (m : G)⁻¹ * (s : G) * (m : G) from rfl, this]
      group
  let e₂ : ↥S ≃* ↥Fb := MulEquiv.ofBijective
    (((QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp S.subtype).codRestrict Fb (fun x => hSP x x.2))
    ⟨fun x y hxy => Subtype.ext (hSinj x.2 y.2 (congrArg Subtype.val hxy)), fun f => by
      obtain ⟨u, hu, huf⟩ := hSont f f.2
      exact ⟨⟨u, hu⟩, Subtype.ext huf⟩⟩
  let e₁ : ↥S ≃* ↥F := Subgroup.equivMapOfInjective S J.subtype J.subtype_injective
  let e : ↥F ≃* ↥Fb := e₁.symm.trans e₂
  have he : ∀ (u : ↥J) (hu : u ∈ S) (hv : (u : G) ∈ F),
      ((e ⟨(u : G), hv⟩ : ↥Fb) : barOf 3 J) = (QuotientGroup.mk u : barOf 3 J) := by
    intro u hu hv
    have h1 : e₁.symm ⟨(u : G), hv⟩ = ⟨u, hu⟩ := by
      rw [MulEquiv.symm_apply_eq]; exact Subtype.ext rfl
    show ((e₂ (e₁.symm ⟨(u : G), hv⟩) : ↥Fb) : barOf 3 J) = _
    rw [h1]; rfl
  have hClaim : ∀ h : ↥J, (h : G) ∈ Subgroup.normalizer (F : Set G) →
      ∀ f ∈ Fb, (QuotientGroup.mk h : barOf 3 J) * f * (QuotientGroup.mk h)⁻¹ ∈ Fb := by
    intro h hh f hf
    obtain ⟨u, hu, rfl⟩ := hSont f hf
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact hSP _ (hconjS h hh u hu)
  have hnormFb : ∀ h : ↥J, (h : G) ∈ Subgroup.normalizer (F : Set G) →
      (QuotientGroup.mk h : barOf 3 J) ∈ Subgroup.normalizer (Fb : Set (barOf 3 J)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨hClaim h hh f, fun hf => ?_⟩
    have hh' : ((h⁻¹ : ↥J) : G) ∈ Subgroup.normalizer (F : Set G) := (Subgroup.normalizer _).inv_mem hh
    have := hClaim h⁻¹ hh' _ hf
    rw [QuotientGroup.mk_inv] at this
    have e : ((QuotientGroup.mk h : barOf 3 J))⁻¹ * ((QuotientGroup.mk h : barOf 3 J) * f *
        ((QuotientGroup.mk h : barOf 3 J))⁻¹) * (((QuotientGroup.mk h : barOf 3 J))⁻¹)⁻¹ = f := by
      group
    rwa [e] at this
  refine ⟨F, hFJ, (hmemF y).2 ⟨⟨y, hyJ⟩, hy₀S, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hua⟩ := (hmemF _).1 a.2
      obtain ⟨v, hv, hvb⟩ := (hmemF _).1 b.2
      have hc := elemAbelian_comm hSel hu hv
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      show (a : G) * b = b * a
      rw [← hua, ← hvb]; exact this
    · obtain ⟨u, hu, rfl⟩ := (hmemF x).1 hx
      have := congrArg Subtype.val (hSel.2 u hu)
      simpa using this
  · rw [Subgroup.card_map_of_injective J.subtype_injective]; exact hScard
  · obtain ⟨fbar, hfbar⟩ := hQ
    have hcongr := autizer_congr (X := J) (T := F) (X' := (⊤ : Subgroup (barOf 3 J))) (T' := Fb) e
      (fun g => by
        have hg : ((⟨g.1, g.2.1⟩ : ↥J) : G) ∈ Subgroup.normalizer (F : Set G) := g.2.2
        refine ⟨⟨QuotientGroup.mk ⟨g.1, g.2.1⟩, trivial, hnormFb _ hg⟩, fun t => ?_⟩
        obtain ⟨u, hu, hut⟩ := (hmemF _).1 t.2
        have hu' := hconjS _ hg u hu
        have hv' : (((⟨g.1, g.2.1⟩ * u * ⟨g.1, g.2.1⟩⁻¹ : ↥J)) : G) ∈ F :=
          (hmemF _).2 ⟨_, hu', rfl⟩
        have ht : t = ⟨(u : G), (hmemF _).2 ⟨u, hu, rfl⟩⟩ := Subtype.ext hut.symm
        have h1 : autAct J F g t = ⟨(((⟨g.1, g.2.1⟩ * u * ⟨g.1, g.2.1⟩⁻¹ : ↥J)) : G), hv'⟩ :=
          Subtype.ext (by rw [autAct_coe, ht]; rfl)
        rw [h1, he _ hu' hv', ht, he _ hu ((hmemF _).2 ⟨u, hu, rfl⟩)]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv])
      (fun g' => by
        obtain ⟨m, hm, hmact⟩ := hact g'.1 g'.2.2
        have hmFm := hmF m hm
        refine ⟨⟨(m : G), m.2, hmFm⟩, fun t => ?_⟩
        obtain ⟨u, hu, hut⟩ := (hmemF _).1 t.2
        have hu' := (Subgroup.mem_normalizer_iff.1 hm u).1 hu
        have hv' : (((m * u * m⁻¹ : ↥J)) : G) ∈ F := (hmemF _).2 ⟨_, hu', rfl⟩
        have ht : t = ⟨(u : G), (hmemF _).2 ⟨u, hu, rfl⟩⟩ := Subtype.ext hut.symm
        have h1 : autAct J F ⟨(m : G), m.2, hmFm⟩ t = ⟨(((m * u * m⁻¹ : ↥J)) : G), hv'⟩ :=
          Subtype.ext (by rw [autAct_coe, ht]; rfl)
        rw [h1, he _ hu' hv', ht, he _ hu ((hmemF _).2 ⟨u, hu, rfl⟩)]
        exact hmact u hu)
    obtain ⟨Φ⟩ := hcongr
    exact ⟨Φ.symm.toMonoidHom.comp fbar, Φ.symm.injective.comp hfbar⟩
  · intro u hu v hv hu1 hv1
    obtain ⟨u₀, hu₀, rfl⟩ := (hmemF u).1 hu
    obtain ⟨v₀, hv₀, rfl⟩ := (hmemF v).1 hv
    have hmk1 : ∀ w ∈ S, (w : ↥J) ≠ 1 → (QuotientGroup.mk w : barOf 3 J) ≠ 1 := by
      intro w hw hw1 h
      exact hw1 (hSinj hw S.one_mem (by rw [h, QuotientGroup.mk_one]))
    have hu1' : u₀ ≠ 1 := fun h => hu1 (by rw [h]; rfl)
    have hv1' : v₀ ≠ 1 := fun h => hv1 (by rw [h]; rfl)
    obtain ⟨nb, hnb, hnbact⟩ := hT _ (hSP u₀ hu₀) _ (hSP v₀ hv₀) (hmk1 u₀ hu₀ hu1') (hmk1 v₀ hv₀ hv1')
    obtain ⟨m, hm, hmact⟩ := hact nb hnb.2
    have hmu : m * u₀ * m⁻¹ = v₀ := by
      have hmem : m * u₀ * m⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hm u₀).1 hu₀
      exact hSinj hmem hv₀ (by rw [hmact u₀ hu₀, hnbact])
    refine ⟨(m : G), ⟨m.2, hmF m hm⟩, ?_⟩
    have : ((m * u₀ * m⁻¹ : ↥J) : G) = (m : G) * (u₀ : G) * (m : G)⁻¹ := rfl
    rw [← this, hmu]

theorem map_center_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') :
    (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Y' := by
  ext y'
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z'
    obtain ⟨z, rfl⟩ := e.surjective z'
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy z]
  · intro h
    refine ⟨e.symm y', fun g => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h (e g)

theorem isFieldAutThree_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {α : MulAut Y} (h : IsFieldAutThree α) : IsFieldAutThree (e.symm.trans (α.trans e)) := by
  have hc := map_center_mulEquiv e
  let ē : Y ⧸ Subgroup.center Y ≃* Y' ⧸ Subgroup.center Y' :=
    QuotientGroup.congr _ _ e hc
  have hē : ∀ y, ē (QuotientGroup.mk y) = QuotientGroup.mk (e y) := fun y =>
    QuotientGroup.congr_mk _ _ e hc y
  have hē' : ∀ y, ē.symm (QuotientGroup.mk (e y)) = QuotientGroup.mk y := fun y =>
    ē.symm_apply_eq.2 (hē y).symm
  rcases h with h | ⟨K, hK, hf, θ, σ, φ, γ, hφ, hθ⟩ | ⟨K, hK, hf, q, θ, σ, φ, γ, hcard, hodd, hφ, hθ⟩
  · left
    ext y'
    simp [h]
  · right; left
    refine ⟨K, hK, hf, ē.symm.trans θ, σ, φ, γ, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (e.symm.trans (α.trans e)) (e y) = e (α y) := by simp
    rw [h1]
    simp only [MulEquiv.trans_apply, hē']
    exact hθ y
  · right; right
    refine ⟨K, hK, hf, q, ē.symm.trans θ, σ, φ, γ, hcard, hodd, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (e.symm.trans (α.trans e)) (e y) = e (α y) := by simp
    rw [h1]
    simp only [MulEquiv.trans_apply, hē']
    exact hθ y

theorem inducesFieldAut_conj_of_mem_normalizer {p : ℕ} {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (h : InducesFieldAut p L x) :
    InducesFieldAut p L (g * x * g⁻¹) := by
  obtain ⟨hx, hf⟩ := h
  have hgx : g * x * g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  refine ⟨hgx, ?_⟩
  have hmul : (⟨g * x * g⁻¹, hgx⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [hmul, map_mul, map_mul, map_inv]
  have := isFieldAutThree_of_mulEquiv (barAut p L ⟨g, hg⟩) hf
  convert this using 1

theorem inducesFieldAut_gLBConj {p : ℕ} {K : Subgroup G} {g b : G}
    (h : InducesFieldAut p K (g * b * g⁻¹)) : InducesFieldAut p (GLBConj g K) b := by
  obtain ⟨hn, hf⟩ := h
  have hb : b ∈ Subgroup.normalizer ((GLBConj g K : Subgroup G) : Set G) := by
    rw [← gLBConj_normalizer, mem_gLBConj]; exact hn
  refine ⟨hb, ?_⟩
  let e := conjQuotEquiv p g K
  have he : ∀ y : ↥K, e (QuotientGroup.mk y) = QuotientGroup.mk (conjEquiv g K y) := fun y =>
    QuotientGroup.congr_mk _ _ (conjEquiv g K) (glaPPrimeCore_map_iso p (conjEquiv g K)) y
  have key : barAut p (GLBConj g K) ⟨b, hb⟩ =
      e.symm.trans ((barAut p K ⟨g * b * g⁻¹, hn⟩).trans e) := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H x' =>
      set y : ↥K := (conjEquiv g K).symm x' with hy
      have hex : e.symm (QuotientGroup.mk x') = QuotientGroup.mk y := by
        rw [MulEquiv.symm_apply_eq, he, hy, MulEquiv.apply_symm_apply]
      simp only [MulEquiv.trans_apply, hex, barAut_mk, he]
      congr 1
      apply Subtype.ext
      have h1 : ((((GLBConj g K).normalizerMonoidHom ⟨b, hb⟩) x' : ↥(GLBConj g K)) : G) =
          b * x' * b⁻¹ := rfl
      have h2 : ((K.normalizerMonoidHom ⟨g * b * g⁻¹, hn⟩ y : ↥K) : G) =
          (g * b * g⁻¹) * y * (g * b * g⁻¹)⁻¹ := rfl
      rw [h1, coe_conjEquiv, h2]
      have h3 : (y : G) = g * x' * g⁻¹ := rfl
      rw [h3]; group
  rw [key]
  exact isFieldAutThree_of_mulEquiv e hf

theorem card_barOf_gLBConj (p : ℕ) (g : G) (K : Subgroup G) :
    Nat.card (barOf p (GLBConj g K)) = Nat.card (barOf p K) :=
  (Nat.card_congr (conjQuotEquiv p g K).toEquiv).symm

theorem l3_gLBConj_iSup₂ (g : G) (P : G → Prop) (f : G → Subgroup G) :
    GLBConj g (⨆ h, ⨆ _ : P h, f h) = ⨆ h, ⨆ _ : P h, GLBConj g (f h) := by
  unfold GLBConj
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]

theorem l3_glaPLayer_gLBConj (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g)

theorem pumpUp_conj {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (x : G) :
    pumpUp L (g⁻¹ * x * g) = GLBConj g (pumpUp L x) := by
  have hC := centralizer_singleton_gLBConj g x
  have hL : GLBConj g L = L := gLBConj_eq_of_mem_normalizer hg
  set T : Subgroup G := GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) with hTdef
  set M : Subgroup G := GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) with hMdef
  have hM : GLAPLayer 3 (Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) = GLBConj g M := by
    rw [hC]; exact l3_glaPLayer_gLBConj 3 g _
  have hT : GLAPLayer 3 (L ⊓ Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) = GLBConj g T := by
    rw [hC, ← l3_glaPLayer_gLBConj 3 g]
    congr 1
    rw [gLBConj_inf, hL]
  have hmemM : ∀ h, h ∈ GLBConj g M ↔ g * h * g⁻¹ ∈ M := fun h => mem_gLBConj
  unfold pumpUp
  rw [hM, hT]
  apply le_antisymm
  · refine iSup₂_le fun h hh => ?_
    have hh' : g * h * g⁻¹ ∈ M := (hmemM h).1 hh
    have e1 : GLBConj h (GLBConj g T) = GLBConj g (GLBConj (g * h * g⁻¹) T) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj]
      congr 1
      group
    rw [e1]
    exact gLBConj_mono g (le_iSup₂ (f := fun (h : G) (_ : h ∈ M) => GLBConj h T) _ hh')
  · rw [l3_gLBConj_iSup₂]
    refine iSup₂_le fun h' hh' => ?_
    have hh : g⁻¹ * h' * g ∈ GLBConj g M := by
      rw [hmemM]; simpa [mul_assoc] using hh'
    have e1 : GLBConj g (GLBConj h' T) = GLBConj (g⁻¹ * h' * g) (GLBConj g T) := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj]
      congr 1
      group
    rw [e1]
    exact le_iSup₂ (f := fun (h : G) (_ : h ∈ GLBConj g M) => GLBConj h (GLBConj g T)) _ hh

theorem glaPComponent_centralizer_conj {p : ℕ} {K : Subgroup G} {g x : G}
    (h : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K) :
    GLAPComponent p (Subgroup.centralizer ({g⁻¹ * x * g} : Set G)) (GLBConj g K) := by
  rw [centralizer_singleton_gLBConj]
  exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj h g

theorem isUpsilonComponent_of_le {B K : Subgroup G} {x : G}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K) (hle : K ≤ upsilonOf B x) :
    IsUpsilonComponent B x K := by
  by_contra hnot
  set X : Subgroup G := Subgroup.centralizer ({x} : Set G) with hX
  set Kb := barX 3 X K with hKb
  let S : Set (Subgroup G) := {L | IsUpsilonComponent B x L}
  have hcomm : ∀ L' ∈ S, ∀ k ∈ Kb, ∀ l ∈ barX 3 X L', l * k = k * l := by
    intro L' hL' k hk l hl
    have hne : K ≠ L' := fun h => hnot (h ▸ hL')
    have hbar : barX 3 X K ≠ barX 3 X L' := fun h => hne (glaPComponent_uniqueAux hK hL'.1 h)
    have h0 := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK.2.2.1 hL'.1.2.2.1 hbar
    have := Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0 hk) l hl
    exact this
  let P : Subgroup G := ((Subgroup.centralizer (Kb : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map X.subtype
  have hSP : upsilonOf B x ≤ P := by
    refine sSup_le fun L' hL' => ?_
    intro l hl
    have hlX : l ∈ X := hL'.1.1 hl
    refine ⟨⟨l, hlX⟩, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨l, hlX⟩ ∈ Subgroup.centralizer (Kb : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hlb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨l, hlX⟩ ∈ barX 3 X L' :=
      ⟨⟨l, hlX⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
    exact (hcomm L' hL' k hk _ hlb).symm
  have hab : ∀ a ∈ Kb, ∀ b ∈ Kb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨⟨k, hkX⟩, hk, rfl⟩ := ha
    have hkK : k ∈ K := (Subgroup.mem_subgroupOf).1 hk
    have hP := hSP (hle hkK)
    obtain ⟨⟨k', hk'X⟩, hk', hk'eq⟩ := hP
    have hkk' : (⟨k', hk'X⟩ : ↥X) = ⟨k, hkX⟩ := Subtype.ext hk'eq
    rw [hkk'] at hk'
    have hk'' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨k, hkX⟩ ∈ Subgroup.centralizer (Kb : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := hk'
    rw [Subgroup.mem_centralizer_iff] at hk''
    exact (hk'' b hb).symm
  have hperf : ⁅Kb, Kb⁆ = Kb := barX_perfect_of_glaPComponent hK
  have hbot : Kb = ⊥ := by
    have h1 : ⁅Kb, Kb⁆ ≤ ⊥ := Subgroup.commutator_le.2 fun a ha b hb => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a ha b hb
    rw [← hperf]; exact le_bot_iff.1 h1
  have hsimple : IsSimpleGroup (↥Kb ⧸ Subgroup.center ↥Kb) := hK.2.2.1.2.2.2
  have hnt : Nontrivial ↥Kb := by
    have := hsimple.toNontrivial
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (↥Kb ⧸ Subgroup.center ↥Kb) := inferInstance
    exact not_subsingleton _ ‹_›
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥Kb)
  have h2 : (a : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ (⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [← hbot]; exact a.2
  exact ha (Subtype.ext (Subgroup.mem_bot.1 h2))

theorem exists_isEkIn_two_of_mem {B A : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hb : b ∈ B)
    (_hb1 : b ≠ 1) (hA : IsEkIn 3 2 B A) :
    ∃ A' : Subgroup G, IsEkIn 3 2 B A' ∧ b ∈ A' ∧ A' ≤ Subgroup.zpowers b ⊔ A := by
  by_cases hbA : b ∈ A
  · exact ⟨A, hA, hbA, le_sup_right⟩
  · have hAB : A ≤ B := hA.1
    have hA3 : Nat.card A = 9 := by simpa using hA.2.2
    have hAne : A ≠ ⊥ := by
      intro h; rw [h, Subgroup.card_bot] at hA3; norm_num at hA3
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
    have haA : (a : G) ∈ A := a.2
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha3 : (a : G) ^ 3 = 1 := hB.2 a (hAB haA)
    have hbl : b ^ 3 = 1 := hB.2 b hb
    have hbz : b ∉ Subgroup.zpowers (a : G) := fun h =>
      hbA ((Subgroup.zpowers_le.2 haA) h)
    have hcard := card_sup_zpowers_of_pow_three_eq_one (H := Subgroup.zpowers (a : G)) hbl hbz
      (fun h hh => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact (Commute.zpow_left (elemAbelian_comm hB (hAB haA) hb : (a : G) * b = b * a) k).eq)
    have hz : Nat.card (Subgroup.zpowers (a : G)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1']
    have hAB' : Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers b ≤ B :=
      sup_le (Subgroup.zpowers_le.2 (hAB haA)) (Subgroup.zpowers_le.2 hb)
    refine ⟨Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers b, ⟨hAB', isElemAbelian_mono hB hAB', ?_⟩,
      (le_sup_right : Subgroup.zpowers b ≤ _) (Subgroup.mem_zpowers b), sup_le ?_ le_sup_left⟩
    · rw [hcard, hz]; norm_num
    · exact (Subgroup.zpowers_le.2 haA).trans le_sup_right

theorem barAut_eq_one_of_centralizes {p : ℕ} {L : Subgroup G} {c : G}
    (hc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcN : c ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨c, hcN⟩ = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk]
    have h1 : ((L.normalizerMonoidHom ⟨c, hcN⟩ x : ↥L) : G) = c * x * c⁻¹ := rfl
    have h2 : c * (x : G) = x * c :=
      (Subgroup.mem_centralizer_iff.1 (hc x.2) c (Set.mem_singleton c))
    have h3 : L.normalizerMonoidHom ⟨c, hcN⟩ x = x := Subtype.ext (by rw [h1, h2]; group)
    simp [h3]

theorem inducesFieldAut_of_mem_sup {L A : Subgroup G} {b : G}
    (hb : L ≤ Subgroup.centralizer ({b} : Set G)) (hbA : ∀ a ∈ A, a * b = b * a)
    (ha : ∀ a ∈ A, InducesFieldAut 3 L a) : ∀ x ∈ Subgroup.zpowers b ⊔ A, InducesFieldAut 3 L x := by
  intro x hx
  have hzA : Subgroup.zpowers b ≤ Subgroup.centralizer (A : Set G) := by
    intro c hc a haA
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (show Commute a b from hbA a haA) k).eq
  obtain ⟨c, hc, a, haA, rfl⟩ := exists_mul_of_mem_sup hzA hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  obtain ⟨hn, hfa⟩ := ha a haA
  have hcl : L ≤ Subgroup.centralizer ({b ^ k} : Set G) := by
    intro l hl c hc
    rw [Set.mem_singleton_iff] at hc; subst hc
    have := Subgroup.mem_centralizer_iff.1 (hb hl) b (Set.mem_singleton b)
    exact (Commute.zpow_left (show Commute b l from this) k).eq
  have hcN : b ^ k ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    have key : ∀ l' ∈ L, b ^ k * l' * (b ^ k)⁻¹ = l' := fun l' hl' => by
      rw [(Subgroup.mem_centralizer_iff.1 (hcl hl') (b ^ k) rfl)]; group
    constructor
    · intro hl; rw [key l hl]; exact hl
    · intro hl
      have h2 := key _ hl
      have h3 : b ^ k * (b ^ k * l * (b ^ k)⁻¹) * (b ^ k)⁻¹ = b ^ k * l * (b ^ k)⁻¹ := h2
      have h4 : b ^ k * l * (b ^ k)⁻¹ = l := by
        calc b ^ k * l * (b ^ k)⁻¹
            = (b ^ k)⁻¹ * (b ^ k * (b ^ k * l * (b ^ k)⁻¹) * (b ^ k)⁻¹) * b ^ k := by group
          _ = (b ^ k)⁻¹ * (b ^ k * l * (b ^ k)⁻¹) * b ^ k := by rw [h3]
          _ = l := by group
      rw [← h4]; exact hl
  refine ⟨Subgroup.mul_mem _ hcN hn, ?_⟩
  have : (⟨b ^ k * a, Subgroup.mul_mem _ hcN hn⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨b ^ k, hcN⟩ * ⟨a, hn⟩ := rfl
  rw [this, map_mul, barAut_eq_one_of_centralizes hcl hcN, one_mul]
  exact hfa

theorem card_sup_of_commute_disjoint {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    (hd : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : H →* G := H.subtype
  let g' : K →* G := K.subtype
  have hcomm : ∀ (m : H) (n : K), Commute (f m) (g' n) := fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod f g' hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    simpa [f, g', disjoint_iff] using hd
  have hrange : (MonoidHom.noncommCoprod f g' hcomm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range]
    simp [f, g']
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem card_facts_sup {B F A : Subgroup G} {y : G} (hB : IsElemAbelian 3 B) (hAB : A ≤ B)
    (hyB : y ∈ B) (hy1 : y ≠ 1) (hyF : y ∈ F) (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 9)
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) (hFA : F ≤ Subgroup.centralizer (A : Set G))
    (hFA0 : F ⊓ A = ⊥) :
    IsElemAbelian 3 (F ⊔ A) ∧ Nat.card ↥(F ⊔ A) = 3 ^ 4 ∧ 4 ≤ CFSG.Open.pRank 3 (F ⊔ A) ∧
      3 ≤ CFSG.Open.pRank 3 (B ⊓ (F ⊔ A)) := by
  have hel : IsElemAbelian 3 (F ⊔ A) := isElemAbelian_sup_of_commute hF hA hFA
  have hcomm : ∀ h ∈ F, ∀ k ∈ A, h * k = k * h := fun h hh k hk =>
    (Subgroup.mem_centralizer_iff.1 (hFA hh) k hk).symm
  have hcard : Nat.card ↥(F ⊔ A) = 3 ^ 4 := by
    rw [card_sup_of_commute_disjoint hcomm hFA0, hFc, hAc]; norm_num
  refine ⟨hel, hcard, CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hel hcard, ?_⟩
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hyA : y ∉ A := fun h => hy1 (by
    have : y ∈ F ⊓ A := ⟨hyF, h⟩
    rw [hFA0] at this; exact this)
  have hcommyA : ∀ h ∈ A, h * y = y * h := fun h hh => elemAbelian_comm hB (hAB hh) hyB
  have hEcard : Nat.card ↥(A ⊔ Subgroup.zpowers y) = 3 ^ 3 := by
    rw [card_sup_zpowers_of_pow_three_eq_one hy3 hyA hcommyA, hAc]; norm_num
  have hEle : A ⊔ Subgroup.zpowers y ≤ B ⊓ (F ⊔ A) :=
    sup_le (le_inf hAB le_sup_right)
      (Subgroup.zpowers_le.2 ⟨hyB, (le_sup_left : F ≤ F ⊔ A) hyF⟩)
  have hEel : IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) :=
    isElemAbelian_mono hB (hEle.trans inf_le_left)
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hEle hEel hEcard

theorem sup_inf_eq_of_le {F A L : Subgroup G} (hFL : F ≤ L) (hFA : F ≤ Subgroup.centralizer (A : Set G))
    (hAL : A ⊓ L = ⊥) : (F ⊔ A) ⊓ L = F := by
  refine le_antisymm ?_ (le_inf le_sup_left hFL)
  rintro z ⟨hz, hzL⟩
  obtain ⟨f, hf, a, ha, rfl⟩ := exists_mul_of_mem_sup hFA hz
  have haL : a ∈ L := by
    have := L.mul_mem (L.inv_mem (hFL hf)) hzL
    simpa using this
  have : a ∈ A ⊓ L := ⟨ha, haL⟩
  rw [hAL] at this
  have ha1 : a = 1 := this
  subst ha1
  simpa using hf

theorem exists_conj_into {F A B J : Subgroup G} {y : G} (hAB : A ≤ B) (hyB : y ∈ B) (hyF : y ∈ F)
    (hy1 : y ≠ 1) (hFJ : F ≤ J) (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hT : ∀ u ∈ F, ∀ v ∈ F, u ≠ 1 → v ≠ 1 →
      ∃ g ∈ J ⊓ Subgroup.normalizer (F : Set G), g * u * g⁻¹ = v) :
    ∀ x ∈ F ⊔ A, ∃ g ∈ J ⊓ Subgroup.normalizer (F : Set G), g * x * g⁻¹ ∈ B ⊓ (F ⊔ A) := by
  intro x hx
  obtain ⟨f, hf, a, ha, rfl⟩ := exists_mul_of_mem_sup (hFJ.trans hJA) hx
  by_cases hf1 : f = 1
  · subst hf1
    refine ⟨1, ⟨J.one_mem, Subgroup.one_mem _⟩, ?_⟩
    simpa using ⟨hAB ha, (le_sup_right : A ≤ F ⊔ A) ha⟩
  · obtain ⟨g, hg, hgf⟩ := hT f hf y hyF hf1 hy1
    refine ⟨g, hg, ?_⟩
    have hga : g * a * g⁻¹ = a := by
      have := Subgroup.mem_centralizer_iff.1 (hJA hg.1) a ha
      rw [← this]; group
    have : g * (f * a) * g⁻¹ = y * a := by
      calc g * (f * a) * g⁻¹ = (g * f * g⁻¹) * (g * a * g⁻¹) := by group
        _ = y * a := by rw [hgf, hga]
    rw [this]
    exact ⟨B.mul_mem hyB (hAB ha), (F ⊔ A).mul_mem ((le_sup_left : F ≤ F ⊔ A) hyF)
      ((le_sup_right : A ≤ F ⊔ A) ha)⟩

end Elem

section Elem2

variable {G : Type} [Group G] [Finite G]

theorem barAut_eq_conj {L : Subgroup G} {z : G} (hn : z ∈ Subgroup.normalizer (L : Set G))
    (hz : z ∈ L) :
    barAut 3 L ⟨z, hn⟩ = MulAut.conj (QuotientGroup.mk (⟨z, hz⟩ : ↥L) : barOf 3 L) := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk]
    show (QuotientGroup.mk (L.normalizerMonoidHom ⟨z, hn⟩ x) : barOf 3 L) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem eq_one_of_mem_core {L : Subgroup G} {z : G} (hz : z ∈ L) (hz3 : z ^ 3 = 1)
    (hcore : (⟨z, hz⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L) : z = 1 := by
  let w : ↥(GLAPPrimeCore 3 ↥L) := ⟨⟨z, hz⟩, hcore⟩
  have hw3 : w ^ 3 = 1 := Subtype.ext (Subtype.ext hz3)
  have hd1 : orderOf w ∣ Nat.card (GLAPPrimeCore 3 ↥L) := orderOf_dvd_natCard w
  have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have h3 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1
  have h4 : w = 1 := orderOf_eq_one_iff.1 h3
  have h6 : z = (((w : ↥(GLAPPrimeCore 3 ↥L)) : ↥L) : G) := rfl
  rw [h6, h4]
  rfl

theorem inf_eq_bot_of_field (iC : InputL3Center) (iF : InputL3FieldInner) {A L : Subgroup G}
    (hty : IsExtremalType (barOf 3 L)) (hA : IsElemAbelian 3 A)
    (hfield : ∀ a ∈ A, InducesFieldAut 3 L a) : A ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hn, hf⟩ := hfield z hz.1
  have hbar : barAut 3 L ⟨z, hn⟩ = MulAut.conj (QuotientGroup.mk (⟨z, hz.2⟩ : ↥L) : barOf 3 L) := by
    ext w
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [barAut_mk]
      show (QuotientGroup.mk (L.normalizerMonoidHom ⟨z, hn⟩ x) : barOf 3 L) = _
      rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  rw [hbar] at hf
  have h1 := iF _ hty _ hf
  have hc : (QuotientGroup.mk (⟨z, hz.2⟩ : ↥L) : barOf 3 L) ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have := congrArg (fun φ : MulAut (barOf 3 L) => φ w) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    set c : barOf 3 L := QuotientGroup.mk (⟨z, hz.2⟩ : ↥L) with hcdef
    have h2 : c * w = w * c := by
      calc c * w = (c * w * c⁻¹) * c := by group
        _ = w * c := by rw [this]
    exact h2.symm
  rw [iC _ hty] at hc
  have hcore : (⟨z, hz.2⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hc)
  let w : ↥(GLAPPrimeCore 3 ↥L) := ⟨⟨z, hz.2⟩, hcore⟩
  have hw3 : w ^ 3 = 1 := Subtype.ext (Subtype.ext (hA.2 z hz.1))
  have hd1 : orderOf w ∣ Nat.card (GLAPPrimeCore 3 ↥L) := orderOf_dvd_natCard w
  have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have h3 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1
  have h4 : w = 1 := orderOf_eq_one_iff.1 h3
  show z = 1
  have h6 : z = (((w : ↥(GLAPPrimeCore 3 ↥L)) : ↥L) : G) := rfl
  rw [h6, h4]
  rfl

theorem not_isStronglyLocallyOneBalanced_of_input (i2027 : Input20_27_2) (iC : InputL3Center)
    {B' L : Subgroup G} {b : G} (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hty : IsExtremalType (barOf 3 L)) (h34 : ¬ IsLThreeFour (barOf 3 L))
    (hB' : IsElemAbelian 3 B') (hN : B' ≤ Subgroup.normalizer (L : Set G))
    (hne : ∃ f ∈ B' ⊓ L, f ≠ 1) : ¬ IsStronglyLocallyOneBalanced 3 B' b L := by
  intro hslob
  obtain ⟨f, hf, hf1⟩ := hne
  have hcenter := iC _ hty
  let π : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)
  let Bt : Subgroup (MulAut (barOf 3 L)) :=
    (B'.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L)
  have hBt3 : IsPGroup 3 Bt := by
    intro β
    obtain ⟨⟨g, hgN⟩, hgB, hβ⟩ := β.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hβ, ← map_pow]
    have : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (hB'.2 g hgB)
    rw [this, map_one]; rfl
  have hBtne : Bt ≠ ⊥ := by
    intro hbot
    have hfN : f ∈ Subgroup.normalizer (L : Set G) := hN hf.1
    have hmem : barAut 3 L ⟨f, hfN⟩ ∈ Bt := ⟨⟨f, hfN⟩, hf.1, rfl⟩
    rw [hbot, Subgroup.mem_bot, barAut_eq_conj hfN hf.2] at hmem
    have hc : (QuotientGroup.mk (⟨f, hf.2⟩ : ↥L) : barOf 3 L) ∈ Subgroup.center (barOf 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have := congrArg (fun φ : MulAut (barOf 3 L) => φ w) hmem
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      set c : barOf 3 L := QuotientGroup.mk (⟨f, hf.2⟩ : ↥L)
      have h2 : c * w = w * c := by
        calc c * w = (c * w * c⁻¹) * c := by group
          _ = w * c := by rw [this]
      exact h2.symm
    rw [hcenter] at hc
    exact hf1 (eq_one_of_mem_core hf.2 (hB'.2 f hf.1)
      ((QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hc)))
  have hperfL : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hperfY : commutator (barOf 3 L) = ⊤ := by
    have hp : Group.IsPerfect L := Subgroup.isPerfect_iff.2 hperfL
    have : Group.IsPerfect (↥L ⧸ GLAPPrimeCore 3 ↥L) := inferInstance
    exact this.1
  obtain ⟨Sb, hSbne, hSbcop, hSbinv⟩ := i2027 _ hperfY hty h34 Bt hBt3 hBtne
  have hinv : ∀ g (hg : g ∈ B') (x : barOf 3 L), x ∈ Sb →
      barAut 3 L ⟨g, hN hg⟩ x ∈ Sb := by
    intro g hg x hx
    have hmem : barAut 3 L ⟨g, hN hg⟩ ∈ Bt := ⟨⟨g, hN hg⟩, hg, rfl⟩
    have := hSbinv _ hmem
    rw [← this]
    exact ⟨x, hx, rfl⟩
  let S : Subgroup G := (Sb.comap π).map L.subtype
  have hmemS : ∀ h, h ∈ S ↔ ∃ hl : h ∈ L, (QuotientGroup.mk (⟨h, hl⟩ : ↥L) : barOf 3 L) ∈ Sb := by
    intro h
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, ht⟩
    · rintro ⟨hl, h2⟩
      exact ⟨⟨h, hl⟩, h2, rfl⟩
  have hSL : S ≤ L := by
    intro h hh
    exact ((hmemS h).1 hh).1
  have hcopS : Nat.Coprime 3 (Nat.card S) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 hd
    have ht3 : (t : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht] at this
      exact congrArg Subtype.val this
    have ht1 : (t : G) ≠ 1 := by
      intro h
      have : t = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht
      norm_num at ht
    obtain ⟨hl, hSt⟩ := (hmemS t).1 t.2
    have hSbg : Nat.Coprime 3 (Nat.card Sb) := hSbcop
    let u : ↥Sb := ⟨QuotientGroup.mk ⟨t, hl⟩, hSt⟩
    have hu3 : u ^ 3 = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk (⟨t, hl⟩ : ↥L) : barOf 3 L) ^ 3 = 1
      rw [← QuotientGroup.mk_pow]
      have : (⟨t, hl⟩ : ↥L) ^ 3 = 1 := Subtype.ext ht3
      rw [this]; rfl
    have hd1 : orderOf u ∣ Nat.card Sb := orderOf_dvd_natCard u
    have hd2 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have h3 : orderOf u = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hSbg) hd1
    have hu1 : u = 1 := orderOf_eq_one_iff.1 h3
    have hmk : (QuotientGroup.mk (⟨t, hl⟩ : ↥L) : barOf 3 L) = 1 := congrArg Subtype.val hu1
    exact ht1 (eq_one_of_mem_core hl ht3 ((QuotientGroup.eq_one_iff _).1 hmk))
  have hSle : S ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
    fun h hh => ⟨Subgroup.le_normalizer (hSL hh), hL.1 (hSL hh)⟩
  have hSfwd : ∀ g (hg : g ∈ B') h, h ∈ S → g * h * g⁻¹ ∈ S := by
    intro g hg h hh
    obtain ⟨hl, hSh⟩ := (hmemS h).1 hh
    have hgN := hN hg
    have hl' : g * h * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgN h).1 hl
    refine (hmemS _).2 ⟨hl', ?_⟩
    have := hinv g hg _ hSh
    rw [barAut_mk] at this
    exact this
  have hnormS : B' ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hSfwd g hg.1 h
    · intro hh
      have := hSfwd g⁻¹ (B'.inv_mem hg.1) _ hh
      simpa [mul_assoc] using this
  have hcomm := hslob S hSle hcopS hnormS
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hSbne
  have hxSb : (x : barOf 3 L) ∈ Sb := x.2
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (x : barOf 3 L)
  have htS : (t : G) ∈ S := (hmemS _).2 ⟨t.2, by simp [ht]⟩
  have hcentral : (x : barOf 3 L) ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    have hc : ⁅(l : G), (t : G)⁆ ∈ GLAPPrimeCoreOf 3 L :=
      hcomm (Subgroup.commutator_mem_commutator l.2 htS)
    have hcl : (⁅l, t⁆ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
      obtain ⟨c, hc1, hc2⟩ := hc
      have : c = ⁅l, t⁆ := Subtype.ext hc2
      rw [← this]; exact hc1
    have h1 : (QuotientGroup.mk ⁅l, t⁆ : barOf 3 L) = 1 := (QuotientGroup.eq_one_iff _).2 hcl
    have h2 : ⁅π l, π t⁆ = 1 := by
      rw [← h1]; exact (map_commutatorElement π l t).symm
    rw [commutatorElement_eq_one_iff_mul_comm] at h2
    rw [← ht]
    exact h2
  rw [hcenter] at hcentral
  exact hx1 (Subtype.ext (Subgroup.mem_bot.1 hcentral))

end Elem2



theorem mem_normalizer_inf_centralizer {G : Type*} [Group G] {L A : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgA : ∀ z ∈ A, g * z * g⁻¹ = z) :
    g ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := (Subgroup.mem_normalizer_iff.1 hgL) h
  have key : ∀ z ∈ A, (z * (g * h * g⁻¹) = (g * h * g⁻¹) * z ↔ z * h = h * z) := by
    intro z hz
    have hz1 : g * z * g⁻¹ = z := hgA z hz
    constructor
    · intro H
      have : g * (z * h) * g⁻¹ = g * (h * z) * g⁻¹ := by
        calc g * (z * h) * g⁻¹ = (g * z * g⁻¹) * (g * h * g⁻¹) := by group
          _ = z * (g * h * g⁻¹) := by rw [hz1]
          _ = (g * h * g⁻¹) * z := H
          _ = (g * h * g⁻¹) * (g * z * g⁻¹) := by rw [hz1]
          _ = g * (h * z) * g⁻¹ := by group
      simpa using this
    · intro H
      calc z * (g * h * g⁻¹) = (g * z * g⁻¹) * (g * h * g⁻¹) := by rw [hz1]
        _ = g * (z * h) * g⁻¹ := by group
        _ = g * (h * z) * g⁻¹ := by rw [H]
        _ = (g * h * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * h * g⁻¹) * z := by rw [hz1]
  simp only [Subgroup.mem_inf, h1, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  refine and_congr Iff.rfl ⟨fun hh z hz => (key z hz).2 (hh z hz), fun hh z hz => (key z hz).1 (hh z hz)⟩

theorem lemma511_of_inputs (h53 : Lemma53) (h56 : Lemma56) (h58 : Lemma58) (h510 : Lemma510)
    (i302 : Input30_2) (i2027 : Input20_27_2) (iC : InputL3Center) (iF : InputL3FieldInner)
    (gJ : Gap_JStructure) (gK : Gap_KxType) (g34 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ),
        GLStanding G m 3 → GLCaseFour G 3 → ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L
        : Subgroup G, IsUpsilonComponent B b L → IsLThreeFour (barOf 3 L) → ∀ A F : Subgroup G,
        IsEkIn 3 2 B A → b ∈ A → (∀ a ∈ A, InducesFieldAut 3 L a) → IsElemAbelian 3 F → Nat.card F =
        9 → F ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) → (∃ y ∈ F ⊓ B, y ≠ 1) → F ⊓ A =
        ⊥ → (∃ f : QuaternionGroup 2 →* autizer (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)))
        F, Function.Injective f) → ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A) b L) : Lemma511 := by
  intro G _ _ m hS hC4 hnot B0 hB0 b0 hb0 hb01 L0 hL0
  by_contra hbad
  classical
  let s : Set (Subgroup G × G × Subgroup G) := {t | IsBZeroMax 3 t.1 ∧ t.2.1 ∈ t.1 ∧ t.2.1 ≠ 1 ∧
    IsUpsilonComponent t.1 t.2.1 t.2.2 ∧ ¬ IsSLThreeEps (barOf 3 t.2.2)}
  have hs : s.Nonempty := ⟨(B0, b0, L0), hB0, hb0, hb01, hL0, hbad⟩
  obtain ⟨⟨B, b, L⟩, ⟨hB, hbB, hb1, hLU, hLnot⟩, hmax⟩ :=
    Set.exists_max_image s (fun t => Nat.card (barOf 3 t.2.2)) (Set.toFinite s) hs
  simp only at hB hbB hb1 hLU hLnot
  have h510' := h510 G m hS hC4 B hB b hbB hb1 L hLU
  have hext : IsExtremalType (barOf 3 L) := h510'.1.resolve_right hLnot
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := (h56 G m hS hC4 B hB b hbB hb1).2 L hLU
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hbL : L ≤ Subgroup.centralizer ({b} : Set G) := hLU.1.1
  obtain ⟨A, hA, hAf⟩ := h510'.2.1
  obtain ⟨A', hA', hbA', hA'le⟩ := exists_isEkIn_two_of_mem hBel hbB hb1 hA
  have hAB : A ≤ B := hA.1
  have hf' : ∀ a ∈ A', InducesFieldAut 3 L a := fun a ha =>
    inducesFieldAut_of_mem_sup hbL (fun a ha => hBel.1.is_comm.comm ⟨a, hAB ha⟩ ⟨b, hbB⟩ |> fun h => by
      simpa using congrArg Subtype.val h) hAf a (hA'le ha)
  have hA'B : A' ≤ B := hA'.1
  have hA'el : IsElemAbelian 3 A' := hA'.2.1
  have hA'c : Nat.card A' = 9 := by simpa using hA'.2.2
  set J : Subgroup G := GLAPLayer 3 (L ⊓ Subgroup.centralizer (A' : Set G)) with hJdef
  have hJle : J ≤ L ⊓ Subgroup.centralizer (A' : Set G) := sSup_le fun K hK => hK.1
  have hJL : J ≤ L := hJle.trans inf_le_left
  have hJA : J ≤ Subgroup.centralizer (A' : Set G) := hJle.trans inf_le_right
  obtain ⟨h3J, hlift⟩ := gJ G m hS hC4 B hB b hbB hb1 L hLU hext A' hA' hbA' hf'
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := by
    intro g hg
    refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer ?_
    refine mem_normalizer_inf_centralizer (hBN hg) fun z hz => ?_
    have := hBel.1.is_comm.comm ⟨g, hg⟩ ⟨z, hA'B hz⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [h2]; group
  have hSC : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB1
  obtain ⟨y, hy, hy1⟩ := exists_mem_inf_ne_one_of_isSCp hSC hBJ h3J
  have hyB : y ∈ B := hy.1
  have hyJ : y ∈ J := hy.2
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hmk1 : (QuotientGroup.mk (⟨y, hyJ⟩ : ↥J) : barOf 3 J) ≠ 1 := by
    intro h
    have hc : (⟨y, hyJ⟩ : ↥J) ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff _).1 h
    have h3 : (⟨y, hyJ⟩ : ↥J) ^ (3 ^ 1) = 1 := Subtype.ext (by simpa using hy3)
    have := l2_eq_one_of_coprime (coprime_card_gLAPPrimeCore_aux 3 ↥J) hc h3
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨Fb, hyFb, hFbel, hFbc, hQ, hT⟩ := i302 (barOf 3 J) _ hmk1 (hlift y hyJ hyB hy1)
  obtain ⟨F, hFJ, hyF, hFel, hFc, hQF, hTF⟩ :=
    exists_lift_of_quotient J y hyJ hy3 hy1 Fb hyFb hFbel hFbc hQ hT
  have hFL : F ≤ L := hFJ.trans hJL
  have hFA : F ≤ Subgroup.centralizer (A' : Set G) := hFJ.trans hJA
  have hAL : A' ⊓ L = ⊥ := inf_eq_bot_of_field iC iF hext hA'el hf'
  have hFA0 : F ⊓ A' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ A' ⊓ L := ⟨hz.2, hFL hz.1⟩
    rw [hAL] at this
    exact this
  obtain ⟨hBsel, hBsc, hBsr4, hBsr3⟩ := card_facts_sup hBel hA'B hyB hy1 hyF hFel hFc hA'el hA'c hFA hFA0
  have hBsL : (F ⊔ A') ⊓ L = F := sup_inf_eq_of_le hFL hFA hAL
  have hBsN : F ⊔ A' ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hFL.trans Subgroup.le_normalizer) (hA'B.trans hBN)
  obtain ⟨hBs1, E, hE, hEven⟩ := h58 G m hS hC4 B hB (F ⊔ A') hBsel hBsr4 hBsr3
  have hbBs : b ∈ F ⊔ A' := (le_sup_right : A' ≤ F ⊔ A') hbA'
  have hnslob : ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A') b L := by
    by_cases h34 : IsLThreeFour (barOf 3 L)
    · exact g34 G m hS hC4 B hB b hbB hb1 L hLU h34 A' F hA' hbA' hf' hFel hFc hFJ
        ⟨y, ⟨hyF, hyB⟩, hy1⟩ hFA0 hQF
    · exact not_isStronglyLocallyOneBalanced_of_input i2027 iC hLU.1 hext h34 hBsel hBsN
        ⟨y, ⟨(le_sup_left : F ≤ F ⊔ A') hyF, hFL hyF⟩, hy1⟩
  refine hnot ⟨F ⊔ A', hBs1, b, hbBs, hb1, L, hLU.1, hnslob, hext, ⟨?_, A', ⟨le_sup_right, hA'el,
    by rw [hA'c]; norm_num⟩, hbA', hf', ?_, ?_⟩, ?_,
    E, ⟨hE.1.trans inf_le_right, hE.2.1, hE.2.2⟩, hEven⟩
  · rw [hBsL]; exact hFc
  · rw [hBsL]; exact hFJ
  · have key : ∀ X : Subgroup G, X = F →
        ∃ f : QuaternionGroup 2 →* autizer J X, Function.Injective f := by
      intro X hX; subst hX; exact hQF
    exact key _ hBsL
  · intro x hx hx1 hxf
    obtain ⟨g, hgJF, hgx⟩ := exists_conj_into hA'B hyB hyF hy1 hFJ hJA hTF x hx
    have hgJ : g ∈ J := hgJF.1
    have hgL : g ∈ L := hJL hgJ
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hgL
    have hx'1 : g * x * g⁻¹ ≠ 1 := by
      intro h; apply hx1; simpa using h
    have hx'B : g * x * g⁻¹ ∈ B := hgx.1
    have hx'f : InducesFieldAut 3 L (g * x * g⁻¹) :=
      inducesFieldAut_conj_of_mem_normalizer hgN hxf
    obtain ⟨hcomp', hfield', -⟩ := h510'.2.2 _ hx'B hx'1 hx'f
    have hle' : pumpUp L (g * x * g⁻¹) ≤ upsilonOf B (g * x * g⁻¹) :=
      h53 G m hS hC4 B hB1 b hbB hb1 L hLU _ hx'B hx'1 hx'f
    have hU' := isUpsilonComponent_of_le hcomp' hle'
    have hnsl' := gK G m hS hC4 B hB b hbB hb1 L hLU hext A' F hA' hbA' hf' hFel hFc hFJ _ hx'B hgx.2 hx'1 hx'f
    have hcard' : Nat.card (barOf 3 (pumpUp L (g * x * g⁻¹))) ≤ Nat.card (barOf 3 L) :=
      hmax (B, g * x * g⁻¹, pumpUp L (g * x * g⁻¹)) ⟨hB, hx'B, hx'1, hU', hnsl'⟩
    have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hpx : pumpUp L x = GLBConj g (pumpUp L (g * x * g⁻¹)) := by
      have := pumpUp_conj hgN (g * x * g⁻¹)
      rwa [← hxeq] at this
    have hgb : g * b * g⁻¹ = b := by
      have h1 : b * g = g * b := Subgroup.mem_centralizer_iff.1 (hbL hgL) b (Set.mem_singleton b)
      rw [← h1]; group
    show GLAPComponent 3 _ (pumpUp L x) ∧ InducesFieldAut 3 (pumpUp L x) b ∧
      Nat.card (barOf 3 (pumpUp L x)) ≤ Nat.card (barOf 3 L)
    rw [hpx]
    refine ⟨?_, ?_, ?_⟩
    · have := glaPComponent_centralizer_conj (g := g) hcomp'
      rwa [← hxeq] at this
    · refine inducesFieldAut_gLBConj ?_
      rw [hgb]; exact hfield'
    · rw [card_barOf_gLBConj]; exact hcard'

end Lemma511Ns
end CFSG.HardMathSupport.Solomon.LocalBalance
