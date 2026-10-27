module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L3Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Irr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3CoverBase

public section

namespace CFSG.QuasithinUnique.A5.Kc3L3

open Matrix CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3Irr

variable {F : Type} [Field F] [CharP F 2]

@[expose] def z2 (F : Type) [Field F] [CharP F 2] : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

@[expose] def emb (w : ↥(evenWeight 5)) : Fin 5 → F := fun i => z2 F (w.1 i)

theorem emb_add (w w' : ↥(evenWeight 5)) : emb (w + w') = (emb w : Fin 5 → F) + emb w' := by
  funext i
  simp [emb]

theorem emb_mem (w : ↥(evenWeight 5)) :
    (emb w : Fin 5 → F) ∈ (delta5 : Submodule F (Fin 5 → F)) := by
  rw [mem_delta5]
  have h : ∑ i, w.1 i = 0 := w.2
  have := congrArg (z2 F) h
  rw [map_sum, map_zero] at this
  exact this

theorem pactF_emb (ρ : Equiv.Perm (Fin 5)) (w : ↥(evenWeight 5)) :
    pactF ρ (emb w : Fin 5 → F) = emb (Delta5.vact ρ w) := by
  funext i
  rfl

@[expose] def gen2 (i : Fin 5) : ↥(evenWeight 5) := ⟨Pi.single i 1 + Pi.single 4 1, Delta5.pair_mem i 4⟩

theorem emb_gen2 (i : Fin 5) : (emb (gen2 i) : Fin 5 → F) = gen i := by
  funext j
  simp [emb, gen2, gen, Pi.single_apply]

theorem decomp2 : ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 →
    w = ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => w i = 1),
      (Pi.single i (1 : ZMod 2) + Pi.single 4 1 : Fin 5 → ZMod 2) := by
  decide +kernel

@[expose] noncomputable def Psi (M : Fin 5 → Matrix (Fin 3) (Fin 3) F) :
    (Fin 5 → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F :=
  ∑ i, (LinearMap.proj i : (Fin 5 → F) →ₗ[F] F).smulRight (M i)

omit [CharP F 2] in
theorem Psi_apply (M : Fin 5 → Matrix (Fin 3) (Fin 3) F) (x : Fin 5 → F) :
    Psi M x = ∑ i, x i • M i := by
  simp [Psi, LinearMap.sum_apply]

omit [CharP F 2] in
theorem Psi_mul_zero {M : Fin 5 → Matrix (Fin 3) (Fin 3) F} (hM : ∀ i j, M i * M j = 0)
    (x y : Fin 5 → F) : Psi M x * Psi M y = 0 := by
  rw [Psi_apply, Psi_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, hM, smul_zero, smul_zero]

theorem Psi_conj {M : Fin 5 → Matrix (Fin 3) (Fin 3) F} (ρ : Equiv.Perm (Fin 5))
    (g g' : Matrix (Fin 3) (Fin 3) F)
    (hgen : ∀ i, Psi M (pactF ρ (gen i)) = g * Psi M (gen i) * g')
    {x : Fin 5 → F} (hx : x ∈ (delta5 : Submodule F (Fin 5 → F))) :
    Psi M (pactF ρ x) = g * Psi M x * g' := by
  have h1 : Psi M (pactF ρ x) = ∑ i, x i • Psi M (pactF ρ (gen i)) := by
    conv_lhs => rw [decomp hx]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
  have h2 : g * Psi M x * g' = ∑ i, x i • (g * Psi M (gen i) * g') := by
    conv_lhs => rw [decomp hx]
    rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, mul_smul_comm, smul_mul_assoc]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => by rw [hgen i]

omit [CharP F 2] in
theorem finrank_mat_le_two (𝒲 : Submodule F (Matrix (Fin 3) (Fin 3) F))
    (h0 : ∀ A ∈ 𝒲, ∀ B ∈ 𝒲, A * B = 0) : Module.finrank F 𝒲 ≤ 2 := by
  have hW : Module.finrank F (Fin 3 → F) = 3 := by simp
  have h1 := Kc3Lin3.finrank_le_two hW
    (𝒲.map (Matrix.toLin' : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] _).toLinearMap) (by
      rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
      show Matrix.toLin' A ∘ₗ Matrix.toLin' B = 0
      rw [← Matrix.toLin'_mul, h0 A hA B hB]
      exact map_zero _)
  have h2 := LinearEquiv.finrank_eq ((Matrix.toLin' : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] _).submoduleMap 𝒲)
  omega

@[expose] def Delta5In {H : Type} [Group H] (V : Subgroup H)
    (β : ↥V ≃* Multiplicative ↥(evenWeight 5)) : Prop :=
  ∀ ρ : Equiv.Perm (Fin 5), Equiv.Perm.sign ρ = 1 → ∃ l : H, (∀ v : ↥V, l * v * l⁻¹ ∈ V) ∧
    ∀ v w : ↥V, (w : H) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact ρ (Multiplicative.toAdd (β v))

section Lifts

variable {H : Type} [Group H] {V : Subgroup H} (β : ↥V ≃* Multiplicative ↥(evenWeight 5))

@[expose] def pt (w : ↥(evenWeight 5)) : H := ((β.symm (Multiplicative.ofAdd w) : ↥V) : H)

theorem pt_add (w w' : ↥(evenWeight 5)) : pt β (w + w') = pt β w * pt β w' := by
  simp [pt, ofAdd_add]

theorem pt_zero : pt β 0 = 1 := by simp [pt]

theorem add_self_evenWeight (w : ↥(evenWeight 5)) : w + w = 0 := by
  apply Subtype.ext
  funext i
  exact CharTwo.add_self_eq_zero (w.1 i)

theorem pt_sq (w : ↥(evenWeight 5)) : pt β w * pt β w = 1 := by
  rw [← pt_add, add_self_evenWeight, pt_zero]

theorem pt_comm (w w' : ↥(evenWeight 5)) : pt β w * pt β w' = pt β w' * pt β w := by
  rw [← pt_add, ← pt_add, add_comm]

theorem pt_ne_one : pt β ⟨Delta5.w0, Delta5.w0_mem⟩ ≠ (1 : H) := by
  intro h
  have h1 : β.symm (Multiplicative.ofAdd (⟨Delta5.w0, Delta5.w0_mem⟩ : ↥(evenWeight 5))) = 1 :=
    Subtype.ext h
  have h2 : (Multiplicative.ofAdd (⟨Delta5.w0, Delta5.w0_mem⟩ : ↥(evenWeight 5))) = 1 := by
    have := congrArg β h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h3 := congrArg (fun y : Multiplicative ↥(evenWeight 5) =>
    ((Multiplicative.toAdd y : ↥(evenWeight 5)) : Fin 5 → ZMod 2) 0) h2
  revert h3
  decide +kernel

variable (φ : H →* X3 F)

@[expose] noncomputable def T (w : ↥(evenWeight 5)) : Matrix (Fin 3) (Fin 3) F := Nm (φ (pt β w))

omit [CharP F 2] in
theorem φ_sq (w : ↥(evenWeight 5)) : φ (pt β w) * φ (pt β w) = 1 := by
  rw [← map_mul, pt_sq, map_one]

omit [CharP F 2] in
theorem φ_comm (w w' : ↥(evenWeight 5)) : φ (pt β w) * φ (pt β w') = φ (pt β w') * φ (pt β w) := by
  rw [← map_mul, ← map_mul, pt_comm]

theorem T_add (w w' : ↥(evenWeight 5)) : T β φ (w + w') = T β φ w + T β φ w' := by
  unfold T
  rw [pt_add, map_mul]
  exact Nm_mul (φ_sq β φ w) (φ_sq β φ w') (φ_comm β φ w w')

theorem T_mul_zero (w w' : ↥(evenWeight 5)) : T β φ w * T β φ w' = 0 :=
  Nm_mul_zero (φ_sq β φ w) (φ_sq β φ w') (φ_comm β φ w w')

theorem T_zero : T β φ 0 = 0 := by
  unfold T
  rw [pt_zero, map_one, Nm_one]

theorem T_eq_Psi (w : ↥(evenWeight 5)) :
    T β φ w = Psi (fun i => T β φ (gen2 i)) (emb w) := by
  classical
  let Tm : ↥(evenWeight 5) →+ Matrix (Fin 3) (Fin 3) F := AddMonoidHom.mk' (T β φ) (T_add β φ)
  have hsum : w = ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => w.1 i = 1), gen2 i := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (decomp2 w.1 w.2)
  have h1 : T β φ w = ∑ i ∈ Finset.univ.filter (fun i : Fin 5 => w.1 i = 1), T β φ (gen2 i) := by
    have := map_sum Tm gen2 (Finset.univ.filter (fun i : Fin 5 => w.1 i = 1))
    rw [← hsum] at this
    exact this
  rw [h1, Psi_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : w.1 i = 0 ∨ w.1 i = 1 := by
    generalize w.1 i = a
    revert a
    decide
  rcases hz with h | h
  · simp [emb, h]
  · simp [emb, h]

end Lifts

section Main

variable {H : Type} [Group H] {V : Subgroup H} (β : ↥V ≃* Multiplicative ↥(evenWeight 5))
  (φ : H →* X3 F)

theorem T_conj (hact : Delta5In V β) {ρ : Equiv.Perm (Fin 5)} (hρ : Equiv.Perm.sign ρ = 1) :
    ∃ g : S3 F, ∀ w : ↥(evenWeight 5),
      T β φ (Delta5.vact ρ w) = mat g * T β φ w * mat g⁻¹ := by
  obtain ⟨l, hl, hact'⟩ := hact ρ hρ
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (φ l)
  refine ⟨g, fun w => ?_⟩
  have hpt : pt β (Delta5.vact ρ w) = l * pt β w * l⁻¹ := by
    set v : ↥V := β.symm (Multiplicative.ofAdd w) with hv
    let w' : ↥V := ⟨l * v * l⁻¹, hl v⟩
    have h1 := hact' v w' rfl
    have h2 : β w' = Multiplicative.ofAdd (Delta5.vact ρ w) := by
      rw [← ofAdd_toAdd (β w'), h1]
      simp [hv]
    have h3 : w' = β.symm (Multiplicative.ofAdd (Delta5.vact ρ w)) := by
      rw [← h2]
      simp
    show ((β.symm (Multiplicative.ofAdd (Delta5.vact ρ w)) : ↥V) : H) = l * (v : H) * l⁻¹
    rw [← h3]
  unfold T
  rw [hpt, map_mul, map_mul, map_inv, ← hg]
  exact Nm_conj g (φ_sq β φ w)

theorem no_delta5 (hφ : Function.Injective φ) (hact : Delta5In V β) : False := by
  classical
  set M : Fin 5 → Matrix (Fin 3) (Fin 3) F := fun i => T β φ (gen2 i) with hM
  have hMM : ∀ i j, M i * M j = 0 := fun i j => T_mul_zero β φ _ _
  have hPsi : ∀ w : ↥(evenWeight 5), Psi M (emb w) = T β φ w := fun w => (T_eq_Psi β φ w).symm
  have hPsigen : ∀ i, Psi M (gen i) = M i := fun i => by rw [← emb_gen2, hPsi]
  have hgenmem : ∀ i, (gen i : Fin 5 → F) ∈ (delta5 : Submodule F (Fin 5 → F)) := fun i => by
    rw [← emb_gen2]
    exact emb_mem _
  have hequi : ∀ ρ : Equiv.Perm (Fin 5), Equiv.Perm.sign ρ = 1 → ∃ g : S3 F,
      ∀ x ∈ (delta5 : Submodule F (Fin 5 → F)),
        Psi M (pactF ρ x) = mat g * Psi M x * mat g⁻¹ := by
    intro ρ hρ
    obtain ⟨g, hg⟩ := T_conj β φ hact hρ
    refine ⟨g, fun x hx => Psi_conj ρ (mat g) (mat g⁻¹) (fun i => ?_) hx⟩
    rw [← emb_gen2, pactF_emb, hPsi, hPsi, hg]
  let K : Submodule F (Fin 5 → F) := delta5 ⊓ LinearMap.ker (Psi M)
  have hKinv : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∀ x ∈ K, pactF σ x ∈ K := by
    intro σ hσ x hx
    obtain ⟨g, hg⟩ := hequi σ hσ
    refine ⟨pactF_mem_delta5 σ hx.1, ?_⟩
    show (Psi M) (pactF σ x) = 0
    rw [hg x hx.1, LinearMap.mem_ker.1 hx.2]
    simp
  by_cases hK : K = ⊥
  · let Ψd : (delta5 : Submodule F (Fin 5 → F)) →ₗ[F] Matrix (Fin 3) (Fin 3) F :=
      (Psi M).domRestrict delta5
    have hinj : Function.Injective Ψd := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have hxK : (x : Fin 5 → F) ∈ K := ⟨x.2, hx⟩
      rw [hK] at hxK
      exact Subtype.ext (Submodule.mem_bot F |>.1 hxK)
    have h4 : Module.finrank F (LinearMap.range Ψd) = 4 := by
      rw [LinearMap.finrank_range_of_inj hinj, finrank_delta5]
    have h2 := finrank_mat_le_two (LinearMap.range Ψd) (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact Psi_mul_zero hMM x y)
    omega
  · have hKd : K = delta5 := irr_delta5 inf_le_left hKinv hK
    have hzero : ∀ x ∈ (delta5 : Submodule F (Fin 5 → F)), Psi M x = 0 := fun x hx => by
      have : x ∈ K := by rw [hKd]; exact hx
      exact LinearMap.mem_ker.1 this.2
    have hM0 : ∀ i, M i = 0 := fun i => by
      rw [← hPsigen i]
      exact hzero _ (hgenmem i)
    let w₀ : ↥(evenWeight 5) := ⟨Delta5.w0, Delta5.w0_mem⟩
    have hT0 : T β φ w₀ = 0 := by
      rw [← hPsi w₀, Psi_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [hM0 i, smul_zero]
    have h1 : φ (pt β w₀) = 1 := eq_one_of_Nm_eq_zero (φ_sq β φ w₀) hT0
    exact pt_ne_one β (hφ (by rw [h1, map_one]))

end Main

end CFSG.QuasithinUnique.A5.Kc3L3

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3L3

theorem delta5In_of_d5 {G : Type} [Group G] {K L V Q : Subgroup G} (hLK : L ≤ K) (hVQ : V ≤ Q)
    (hQL : Q ≤ L) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (β : ↥V ≃* Multiplicative ↥(evenWeight 5))
    (hβ : ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) =
        Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β v))) :
    Delta5In (V.subgroupOf K)
      ((Subgroup.subgroupOfEquivOfLe (hVQ.trans (hQL.trans hLK))).trans β) := by
  intro ρ hρ
  have hρA : ρ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hρ
  obtain ⟨l, hl⟩ := hα ⟨ρ, hρA⟩
  have hlρ : ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = ρ :=
    congrArg Subtype.val hl
  have hlK : (l : G) ∈ K := hLK l.2
  refine ⟨⟨(l : G), hlK⟩, ?_, ?_⟩
  · intro v
    have hv : ((v : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
    have h1 := (Subgroup.mem_normalizer_iff.1 (hLV l.2) ((v : ↥K) : G)).1 hv
    exact Subgroup.mem_subgroupOf.2 (by simpa using h1)
  · intro v w hw
    have hvG : ((v : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
    have hwG : ((w : ↥K) : G) ∈ V := Subgroup.mem_subgroupOf.1 w.2
    have hw' : ((w : ↥K) : G) = l * ((v : ↥K) : G) * l⁻¹ := by
      have := congrArg Subtype.val hw
      simpa using this
    have := hβ l ⟨_, hvG⟩ ⟨_, hwG⟩ hw'
    rw [hlρ] at this
    exact this

theorem kc3ForS_psl3 : Kc3ForS Kc3PSL3 := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hD hperf hSL hS hT hST hTK hTS
  exfalso
  obtain ⟨f, hf, -, F, _, _, hF, ⟨e⟩⟩ := hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  exact no_delta5 ((Subgroup.subgroupOfEquivOfLe hVK).trans β) e.toMonoidHom e.injective
    (delta5In_of_d5 hLK hVQ hQL hLV α hα β hβ)

theorem kc3For_psl3
    : Kc3For Kc3PSL3 := kc3For_of_simple isoInv_psl3 kc3ForS_psl3

end CFSG.QuasithinUnique.A5
