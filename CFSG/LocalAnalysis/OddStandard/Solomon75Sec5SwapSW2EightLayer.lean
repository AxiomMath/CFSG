module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapCentral
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracEng
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section EightLayer

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem bcdLayer_mem_oddCoreOf_iff_subtype {C : Subgroup X} (x : ↥C) :
    (x : X) ∈ oddCoreOf C ↔ x ∈ pPrimeCore 2 ↥C :=
  ⟨fun h => (mem_oddCoreOf_iff.1 h).2, fun h => mem_oddCoreOf_iff.2 ⟨x.2, h⟩⟩

private theorem bcdLayer_comm_gen {Q : Type*} [Group Q] {Λ P : Subgroup Q} {g : Q}
    (hgΛ : ∀ x ∈ Λ, g * x * g⁻¹ ∈ Λ) (hP : IsPGroup 2 ↥P) (hV : ∀ x ∈ Λ, ⁅x, g⁆ ∈ P) :
    ∃ R : Subgroup Q, R ≤ Λ ∧ (∀ q ∈ Λ, ∀ r ∈ R, q * r * q⁻¹ ∈ R) ∧ IsPGroup 2 ↥R ∧
      ∀ x ∈ Λ, ⁅x, g⁆ ∈ R := by
  classical
  let T : Set Q := {c | ∃ x ∈ Λ, c = ⁅x, g⁆}
  refine ⟨Subgroup.closure T, ?_, ?_, ?_, fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have e : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Λ.mul_mem hx (hgΛ _ (Λ.inv_mem hx))
  · intro q hq r hr
    induction hr using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, rfl⟩ := hc
      have e : q * ⁅x, g⁆ * q⁻¹ = ⁅q * x, g⁆ * (⁅q, g⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.closure T).mul_mem (Subgroup.subset_closure ⟨_, Λ.mul_mem hq hx, rfl⟩)
        ((Subgroup.closure T).inv_mem (Subgroup.subset_closure ⟨_, hq, rfl⟩))
    | one => simp
    | mul a b _ _ ha hb =>
      have : q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) := by group
      rw [this]; exact (Subgroup.closure T).mul_mem ha hb
    | inv a _ ha =>
      have : q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ := by group
      rw [this]; exact (Subgroup.closure T).inv_mem ha
  · refine hP.to_le ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hV x hx

private theorem bcdLayer_mk_comm_mem {C W : Subgroup X} {t : X} (htC : t ∈ C) {c : ↥C}
    (hV : ∃ w ∈ W, ⁅(c : X), t⁆ * w⁻¹ ∈ oddCoreOf C) :
    ⁅QuotientGroup.mk' (pPrimeCore 2 ↥C) c, QuotientGroup.mk' (pPrimeCore 2 ↥C) ⟨t, htC⟩⁆ ∈
      (W.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) := by
  obtain ⟨w, hwW, hwo⟩ := hV
  obtain ⟨hmem, hmemP⟩ := mem_oddCoreOf_iff.1 hwo
  have hcmem : ⁅(c : X), t⁆ ∈ C := (⁅c, (⟨t, htC⟩ : ↥C)⁆ : ↥C).2
  have hwC : w ∈ C := by
    have h1 := C.mul_mem (C.inv_mem hcmem) hmem
    have e : (⁅(c : X), t⁆)⁻¹ * (⁅(c : X), t⁆ * w⁻¹) = w⁻¹ := by group
    rw [e] at h1
    simpa using C.inv_mem h1
  refine ⟨⟨w, hwC⟩, hwW, ?_⟩
  have h1 : (⁅c, (⟨t, htC⟩ : ↥C)⁆ * (⟨w, hwC⟩ : ↥C)⁻¹ : ↥C) ∈ pPrimeCore 2 ↥C := hmemP
  have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥C)
      (⁅c, (⟨t, htC⟩ : ↥C)⁆ * (⟨w, hwC⟩ : ↥C)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h1
  rw [map_mul, map_inv, mul_inv_eq_one, map_commutatorElement] at h2
  exact h2.symm

private theorem bcdLayer_le_LPlusIn {D F : Subgroup X} (hF : IsPCompIn 2 D F) :
    F ≤ LPlusIn D := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  refine ⟨⟨m, hF.1 hm⟩, ?_, rfl⟩
  rw [LPlus_eq_pLayer_sup_NPlus]
  exact Subgroup.mem_sup_left ((le_sSup hF.2 : F.subgroupOf D ≤ pLayer ↥D 2) hm)

theorem swap_contra_of_odd {C F : Subgroup X} {t : X} (ht2 : t * t = 1) (htC : t ∈ C)
    (hF : IsPCompIn 2 C F) (hF' : IsPCompIn 2 C (F.map (MulAut.conj t).toMonoidHom))
    (hne : F.map (MulAut.conj t).toMonoidHom ≠ F) {W : Subgroup X} (hW : IsPGroup 2 ↥W)
    (hV : ∀ x ∈ F ⊔ F.map (MulAut.conj t).toMonoidHom, ∃ w ∈ W, ⁅x, t⁆ * w⁻¹ ∈ oddCoreOf C) :
    False := by
  classical
  set F' : Subgroup X := F.map (MulAut.conj t).toMonoidHom with hF'def
  have hFC : F ≤ C := hF.1
  have hF'C : F' ≤ C := hF'.1
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K₁ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (F.subgroupOf C).map π with hK₁
  set K₂ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (F'.subgroupOf C).map π with hK₂
  have hK₁c : IsComponent K₁ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hF.2
    show IsComponent ((F.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₂c : IsComponent K₂ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hF'.2
    show IsComponent ((F'.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₁₂ : K₁ ≠ K₂ := by
    intro heq
    apply hne
    have h1 := eq_of_map_pPrimeCore_eq hF'.2 hF.2 heq.symm
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hF'C, inf_of_le_left hFC] at h1
    exact h1
  have hcomm₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb =>
    commute_of_ne hK₁c hK₂c hK₁₂ ha hb
  set g : ↥C ⧸ pPrimeCore 2 ↥C := π ⟨t, htC⟩ with hg
  have hgK₁ : ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₂ := by
    rintro _ ⟨ec, hec, rfl⟩
    have hse : t * (ec : X) * t⁻¹ ∈ F' := ⟨ec, hec, rfl⟩
    refine ⟨⟨t, htC⟩ * ec * ⟨t, htC⟩⁻¹, hse, ?_⟩
    simp only [hg, map_mul, map_inv]
  have hgK₂ : ∀ k ∈ K₂, g * k * g⁻¹ ∈ K₁ := by
    rintro _ ⟨ec, hec, rfl⟩
    obtain ⟨e, he, hee⟩ := (hec : (ec : X) ∈ F')
    have hte : t * (ec : X) * t⁻¹ = e := by
      have hee' : t * e * t⁻¹ = (ec : X) := hee
      rw [← hee']
      calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t * t)⁻¹ := by group
        _ = e := by rw [ht2]; simp
    refine ⟨⟨t, htC⟩ * ec * ⟨t, htC⟩⁻¹, ?_, ?_⟩
    · show t * (ec : X) * t⁻¹ ∈ F
      rw [hte]
      exact he
    · simp only [hg, map_mul, map_inv]
  have hgΛ : ∀ x ∈ K₁ ⊔ K₂, g * x * g⁻¹ ∈ K₁ ⊔ K₂ := by
    have h1 : K₁ ≤ (K₁ ⊔ K₂).comap (MulAut.conj g).toMonoidHom := fun x hx =>
      Subgroup.mem_sup_right (hgK₁ x hx)
    have h2 : K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj g).toMonoidHom := fun x hx =>
      Subgroup.mem_sup_left (hgK₂ x hx)
    intro x hx
    exact (sup_le h1 h2 : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj g).toMonoidHom) hx
  set Wb : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (W.subgroupOf C).map π with hWb
  have hWbp : IsPGroup 2 ↥Wb := (hW.comap_subtype).map π
  have hΛ : ((F ⊔ F').subgroupOf C).map π = K₁ ⊔ K₂ := by
    rw [Subgroup.subgroupOf_sup hFC hF'C, Subgroup.map_sup]
  have hcomm : ∀ x ∈ K₁ ⊔ K₂, ⁅x, g⁆ ∈ Wb := by
    intro x hx
    rw [← hΛ] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact bcdLayer_mk_comm_mem htC (hV (c : X) hc)
  obtain ⟨R, hRΛ, hRn, hRp, hRmem⟩ := bcdLayer_comm_gen hgΛ hWbp hcomm
  refine swap_central_contra hK₁c.1 hcomm₁₂ hRΛ hRn hRp ?_
  intro k hk
  refine ⟨g * k * g⁻¹, hgK₁ k hk, ?_⟩
  have e : k * (g * k * g⁻¹)⁻¹ = ⁅k, g⁆ := by simp only [commutatorElement_def]; group
  rw [e]
  exact hRmem k (Subgroup.mem_sup_left hk)

theorem comp_centralized_of_commutators_two {C F : Subgroup X} {t : X} (ht2 : t * t = 1)
    (htC : t ∈ C) (hF : IsPCompIn 2 C F) {W : Subgroup X} (hW : IsPGroup 2 ↥W)
    (hV : ∀ x ∈ F ⊔ F.map (MulAut.conj t).toMonoidHom, ∃ w ∈ W, ⁅x, t⁆ * w⁻¹ ∈ oddCoreOf C) :
    t ∈ normalizer (F : Set X) ∧ ∀ f ∈ F, ⁅f, t⁆ ∈ oddCoreOf C := by
  classical
  have htN : t ∈ normalizer (F : Set X) := by
    refine mem_normalizer_of_map_conj_eq ?_
    by_contra hne
    refine swap_contra_of_odd ht2 htC hF ?_ hne hW hV
    have h := Stage1.Thm2.Recip.isPCompIn_map_conj hF t
    rwa [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer htC)] at h
  refine ⟨htN, ?_⟩
  have hFC : F ≤ C := hF.1
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (F.subgroupOf C).map π with hK
  have hKc : IsComponent K := by
    obtain ⟨K', hK', -, hKeq, -⟩ := hF.2
    show IsComponent ((F.subgroupOf C).map π)
    rw [hKeq]
    exact hK'
  set g : ↥C ⧸ pPrimeCore 2 ↥C := π ⟨t, htC⟩ with hg
  have hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    rintro _ ⟨ec, hec, rfl⟩
    refine ⟨⟨t, htC⟩ * ec * ⟨t, htC⟩⁻¹, ?_, ?_⟩
    · show t * (ec : X) * t⁻¹ ∈ F
      exact (Subgroup.mem_normalizer_iff.1 htN _).1 hec
    · simp only [hg, map_mul, map_inv]
  set Wb : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (W.subgroupOf C).map π with hWb
  have hWbp : IsPGroup 2 ↥Wb := (hW.comap_subtype).map π
  have hcomm : ∀ x ∈ K, ⁅x, g⁆ ∈ Wb := by
    rintro _ ⟨c, hc, rfl⟩
    exact bcdLayer_mk_comm_mem htC (hV (c : X) (Subgroup.mem_sup_left hc))
  obtain ⟨R, hRK, hRn, hRp, hRmem⟩ := bcdLayer_comm_gen hgK hWbp hcomm
  have hcen : ∀ x ∈ R, ∀ y ∈ K, Commute y x := by
    have hN := normal_subgroupOf_inf hRn
    have hp : IsPGroup 2 ↥((R ⊓ K).subgroupOf K) :=
      (hRp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hcen := normal_pgroup_le_center_of_quasisimple hKc.1 hp
    intro x hx y hy
    have hx' : (⟨x, hRK hx⟩ : ↥K) ∈ (R ⊓ K).subgroupOf K := ⟨hx, hRK hx⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hx') ⟨y, hy⟩)
  have hKt : ∀ k ∈ K, Commute g k := by
    refine commute_of_central_comm (commutator_eq_self_of_quasisimple hKc.1) hgK ?_
    intro k hk x hx
    have e : k⁻¹ * (g * k * g⁻¹) = ⁅k⁻¹, g⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    exact hcen _ (hRmem _ (K.inv_mem hk)) x hx
  intro f hf
  set c : ↥C := ⟨f, hFC hf⟩ with hc
  have hcK : π c ∈ K := ⟨c, hf, rfl⟩
  have h1 : π ⁅c, (⟨t, htC⟩ : ↥C)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hKt _ hcK).symm.eq
  exact (bcdLayer_mem_oddCoreOf_iff_subtype ⁅c, (⟨t, htC⟩ : ↥C)⁆).2
    ((QuotientGroup.eq_one_iff _).1 h1)

theorem le_pLayer_of_isPCompIn_inf {s r : X} (hs2 : s ^ 2 = 1) (hsr : s * r = r * s)
    {Δ : Subgroup X}
    (hΔ : IsPCompIn 2 (centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X)) Δ) :
    Δ ≤ (pLayer ↥(centralizer ({r} : Set X)) 2).map (centralizer ({r} : Set X)).subtype := by
  set D : Subgroup X := centralizer ({r} : Set X) with hD
  set Cu : Subgroup X := centralizer ({s} : Set X) with hCu
  have hΔCu : Δ ≤ Cu := hΔ.1.trans inf_le_left
  have hΔD : Δ ≤ D := hΔ.1.trans inf_le_right
  have huD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2 hsr
  set uD : ↥D := ⟨s, huD⟩ with huDdef
  have hcen : centralizer ({uD} : Set ↥D) = Cu.subgroupOf D := centralizer_singleton_subgroup huD
  have hEC_D : Δ.subgroupOf D ≤ centralizer ({uD} : Set ↥D) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono D hΔCu
  have hE_D : IsPComponent 2 ((Δ.subgroupOf D).subgroupOf (centralizer ({uD} : Set ↥D))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hΔCu hΔD).2 hΔ.2
  have hu2 : uD ^ 2 = 1 := by
    apply Subtype.ext
    exact hs2
  have hB : IsPGroup 2 (Subgroup.zpowers uD) := aux_isPGroup_zpowers_of_sq hu2
  have hbal := layer_balance (Subgroup.zpowers uD) hB
  have hcz : centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) =
      centralizer ({uD} : Set ↥D) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hEC_D' : Δ.subgroupOf D ≤ centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D) := by
    rw [hcz]
    exact hEC_D
  have hE_D' : IsPComponent 2 ((Δ.subgroupOf D).subgroupOf
      (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) : Set ↥D))) := by
    rw [hcz]
    exact hE_D
  have h1 := le_sSup (s := {L | IsPComponent 2 L}) hE_D'
  have h2 := Subgroup.map_mono (f := (centralizer ((Subgroup.zpowers uD : Subgroup ↥D) :
    Set ↥D)).subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hEC_D'] at h2
  have hEL : Δ.subgroupOf D ≤ pLayer ↥D 2 := h2.trans hbal
  intro m hm
  exact ⟨⟨m, hΔD hm⟩, hEL (Subgroup.mem_subgroupOf.2 hm), rfl⟩

theorem s_centralizes_layer (h : Sec5Data X n z Z S) {s y : X} (hs : IsSec5Inv X Z s)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hys : y * s = s * y)
    (hcon : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({y} : Set X)) ≠ ⊥) :
    ∀ x ∈ (pLayer ↥(centralizer ({y} : Set X)) 2).map (centralizer ({y} : Set X)).subtype,
      ⁅x, s⁆ ∈ oddCoreOf (centralizer ({y} : Set X)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2' : y ^ 2 = 1 := by rw [sq]; exact hy2
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2' hy1
  obtain ⟨W, hW, hWn, hV⟩ := exists_mirror_comm h hs hyo hys hcon
  set D : Subgroup X := centralizer ({y} : Set X) with hD
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 (LPlusIn D) with h𝒪
  have hsD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2 hys.symm
  have hDn : D ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have h𝒪D : 𝒪 ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized ((Subgroup.map_subtype_le _).trans (LPlusIn_le D)) hDn
      (odd_card_oddCoreOf _)
  have hsmap : D.map (MulAut.conj s).toMonoidHom = D :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsD)
  have hcomp : ∀ F : Subgroup X, IsPCompIn 2 D F → ∀ f ∈ F, ⁅f, s⁆ ∈ oddCoreOf D := by
    intro F hF f hf
    have hF' : IsPCompIn 2 D (F.map (MulAut.conj s).toMonoidHom) := by
      have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hF s
      rwa [hsmap] at h1
    have hFL : F ⊔ F.map (MulAut.conj s).toMonoidHom ≤ LPlusIn D :=
      sup_le (bcdLayer_le_LPlusIn hF) (bcdLayer_le_LPlusIn hF')
    refine (comp_centralized_of_commutators_two hs.sq hsD hF hW ?_).2 f hf
    intro x hx
    obtain ⟨o, ho, w, hw, hxw⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing 𝒪 W hWn _).1 (hV x (hFL hx))
    refine ⟨w, hw, ?_⟩
    have e : ⁅x, s⁆ * w⁻¹ = o := by rw [← hxw]; group
    rw [e]
    exact h𝒪D ho
  have hS : ∀ A ∈ {F : Subgroup X | IsPCompIn 2 D F}, A ≤ normalizer (oddCoreOf D : Set X) :=
    fun A hA => hA.1.trans (le_normalizer_oddCoreOf D)
  have hall := forall_comm_mem_of_sSup (le_normalizer_oddCoreOf D hsD) hS
    (fun A hA a ha => hcomp A hA a ha)
  have hle : (pLayer ↥D 2).map D.subtype ≤ sSup {F : Subgroup X | IsPCompIn 2 D F} := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hLD : IsPCompIn 2 D (L.map D.subtype) := by
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      have e : (L.map D.subtype).subgroupOf D = L :=
        Subgroup.comap_map_eq_self_of_injective D.subtype_injective L
      rw [e]
      exact hL
    exact le_sSup hLD
  intro x hx
  exact hall x (hle hx)

end EightLayer

end CFSG.OddStandard.Solomon75
