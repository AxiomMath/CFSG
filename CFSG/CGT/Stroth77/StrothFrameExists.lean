module

public import CFSG.CGT.Stroth77.StrothFrame
public import CFSG.CGT.Stroth77.NonSplitCore.Recognize
public import CFSG.CGT.Stroth77.NonSplit.StrothT
public import CFSG.CGT.Stroth77.NonSplit.Type100Mns
public import CFSG.Holt.H78.Prelim
public import CFSG.CGT.Stroth77.Section1Structure

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)
open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator

section Map

variable {H K : Type*} [Group H] [Group K] {B : Subgroup H} {τ : StrothTypeIndex}

theorem map_mem_normalizer_map (f : H →* K) {g : H} (hg : g ∈ Subgroup.normalizer B) :
    f g ∈ Subgroup.normalizer (B.map f) :=
  Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩

theorem equivMapOfInjective_conjBy (f : H →* K) (hf : Function.Injective f) {g : H}
    (hg : g ∈ Subgroup.normalizer B) (b : B) :
    B.equivMapOfInjective f hf (conjBy hg b) =
      conjBy (map_mem_normalizer_map f hg) (B.equivMapOfInjective f hf b) := by
  apply Subtype.ext
  simp [conjBy, Subgroup.coe_equivMapOfInjective_apply]

@[expose] noncomputable def StrothWeakTypeData.map (D : StrothWeakTypeData B τ) (f : H →* K)
    (hf : Function.Injective f) : StrothWeakTypeData (B.map f) τ where
  e := (MulEquiv.toAdditive (B.equivMapOfInjective f hf).symm).trans D.e
  uv := f D.uv
  t := f D.t
  u := f D.u
  ρ := f D.ρ
  uv_sq := by rw [← map_mul, D.uv_sq, map_one]
  t_sq := by rw [← map_mul, D.t_sq, map_one]
  uv_comm_t := by rw [← map_mul, D.uv_comm_t, map_mul]
  rho_odd := by rw [orderOf_injective f hf]; exact D.rho_odd
  u_sq := by rw [← map_mul, D.u_sq, map_one]
  u_rho := by rw [← map_mul, ← map_mul, ← map_mul, D.u_rho, map_one]
  uv_rho := by rw [← map_mul, D.uv_rho, map_mul]
  t_rho := by rw [← map_mul, D.t_rho, map_mul, map_mul]
  uv_comm_u := by rw [← map_mul, D.uv_comm_u, map_mul]
  t_u := by rw [← map_mul, D.t_u, map_mul, map_mul]
  uv_mem := map_mem_normalizer_map f D.uv_mem
  t_mem := map_mem_normalizer_map f D.t_mem
  u_mem := map_mem_normalizer_map f D.u_mem
  ρ_mem := map_mem_normalizer_map f D.ρ_mem
  uv_conj := fun y => by
    obtain ⟨b, rfl⟩ := (B.equivMapOfInjective f hf).surjective y
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
      ← equivMapOfInjective_conjBy f hf D.uv_mem, MulEquiv.symm_apply_apply]
    exact D.uv_conj b
  t_conj := fun y => by
    obtain ⟨b, rfl⟩ := (B.equivMapOfInjective f hf).surjective y
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
      ← equivMapOfInjective_conjBy f hf D.t_mem, MulEquiv.symm_apply_apply]
    exact D.t_conj b
  u_conj := fun y => by
    obtain ⟨b, rfl⟩ := (B.equivMapOfInjective f hf).surjective y
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
      ← equivMapOfInjective_conjBy f hf D.u_mem, MulEquiv.symm_apply_apply]
    exact D.u_conj b
  ρ_conj := fun y => by
    obtain ⟨b, rfl⟩ := (B.equivMapOfInjective f hf).surjective y
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
      ← equivMapOfInjective_conjBy f hf D.ρ_mem, MulEquiv.symm_apply_apply]
    exact D.ρ_conj b

end Map

section OfMap

variable {H Q : Type*} [Group H] [Group Q] {B : Subgroup H} {τ : StrothTypeIndex}

@[expose] noncomputable def equivMapOfInjOn (f : H →* Q) (hf : Function.Injective (f.comp B.subtype)) :
    B ≃* B.map f :=
  (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

@[simp] theorem coe_equivMapOfInjOn (f : H →* Q) (hf : Function.Injective (f.comp B.subtype))
    (b : B) : (equivMapOfInjOn f hf b : Q) = f b := rfl

@[expose] noncomputable def StrothWeakTypeData.ofMap (f : H →* Q)
    (hf : Function.Injective (f.comp B.subtype)) {B' : Subgroup Q} (hB : B.map f = B')
    (D' : StrothWeakTypeData B' τ)
    {uv t u ρ : H} (huv : f uv = D'.uv) (ht : f t = D'.t) (hu : f u = D'.u) (hρ : f ρ = D'.ρ)
    (uv_sq : uv * uv = 1) (t_sq : t * t = 1) (uv_comm_t : uv * t = t * uv)
    (rho_odd : Odd (orderOf ρ)) (u_sq : u * u = 1) (u_rho : u * ρ * u * ρ = 1)
    (uv_rho : uv * ρ = ρ * t) (t_rho : t * ρ = ρ * uv * t) (uv_comm_u : uv * u = u * uv)
    (t_u : t * u = u * uv * t) (uv_mem : uv ∈ Subgroup.normalizer B)
    (t_mem : t ∈ Subgroup.normalizer B) (u_mem : u ∈ Subgroup.normalizer B)
    (ρ_mem : ρ ∈ Subgroup.normalizer B) : StrothWeakTypeData B τ :=
  have key : ∀ {g : H} (hg : g ∈ Subgroup.normalizer B) {g' : Q}
      (hg' : g' ∈ Subgroup.normalizer B'), f g = g' → ∀ b : B,
      ((equivMapOfInjOn f hf).trans (MulEquiv.subgroupCongr hB)) (conjBy hg b) =
        conjBy hg' (((equivMapOfInjOn f hf).trans (MulEquiv.subgroupCongr hB)) b) := by
    intro g hg g' hg' hgg' b
    apply Subtype.ext
    simp [conjBy, ← hgg']
  { e := (MulEquiv.toAdditive ((equivMapOfInjOn f hf).trans (MulEquiv.subgroupCongr hB))).trans
      D'.e
    uv := uv
    t := t
    u := u
    ρ := ρ
    uv_sq := uv_sq
    t_sq := t_sq
    uv_comm_t := uv_comm_t
    rho_odd := rho_odd
    u_sq := u_sq
    u_rho := u_rho
    uv_rho := uv_rho
    t_rho := t_rho
    uv_comm_u := uv_comm_u
    t_u := t_u
    uv_mem := uv_mem
    t_mem := t_mem
    u_mem := u_mem
    ρ_mem := ρ_mem
    uv_conj := fun b => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
        key uv_mem D'.uv_mem huv]
      exact D'.uv_conj _
    t_conj := fun b => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
        key t_mem D'.t_mem ht]
      exact D'.t_conj _
    u_conj := fun b => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
        key u_mem D'.u_mem hu]
      exact D'.u_conj _
    ρ_conj := fun b => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
        key ρ_mem D'.ρ_mem hρ]
      exact D'.ρ_conj _ }

theorem StrothWeakTypeData.map_ofMap_e_symm (f : H →* Q)
    (hf : Function.Injective (f.comp B.subtype)) {B' : Subgroup Q} (hB : B.map f = B')
    (D' : StrothWeakTypeData B' τ)
    {uv t u ρ : H} (huv : f uv = D'.uv) (ht : f t = D'.t) (hu : f u = D'.u) (hρ : f ρ = D'.ρ)
    (uv_sq : uv * uv = 1) (t_sq : t * t = 1) (uv_comm_t : uv * t = t * uv)
    (rho_odd : Odd (orderOf ρ)) (u_sq : u * u = 1) (u_rho : u * ρ * u * ρ = 1)
    (uv_rho : uv * ρ = ρ * t) (t_rho : t * ρ = ρ * uv * t) (uv_comm_u : uv * u = u * uv)
    (t_u : t * u = u * uv * t) (uv_mem : uv ∈ Subgroup.normalizer B)
    (t_mem : t ∈ Subgroup.normalizer B) (u_mem : u ∈ Subgroup.normalizer B)
    (ρ_mem : ρ ∈ Subgroup.normalizer B) (y : Torus τ.k) :
    f ((Additive.toMul ((StrothWeakTypeData.ofMap f hf hB D' huv ht hu hρ uv_sq t_sq uv_comm_t
      rho_odd u_sq u_rho uv_rho t_rho uv_comm_u t_u uv_mem t_mem u_mem ρ_mem).e.symm y) : B) : H) =
      ((Additive.toMul (D'.e.symm y) : B') : Q) := by
  have h := congrArg (fun z : B' => (z : Q))
    (((equivMapOfInjOn f hf).trans (MulEquiv.subgroupCongr hB)).apply_symm_apply
      (Additive.toMul (D'.e.symm y)))
  exact h

end OfMap

section MnsData

@[expose] noncomputable def toAHom : Torus (Type100.k 1) →+ Additive ↥Ag :=
  AddMonoidHom.mk' (fun x => Additive.ofMul ⟨toA x, mem_Ag.2 (toA_mem x)⟩) fun x y => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact toA_add x y

theorem toAHom_bijective : Function.Bijective toAHom := by
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro x y h
    apply toA_injective
    have := congrArg (fun z : Additive ↥Ag => ((Additive.toMul z : ↥Ag) : Mns)) h
    simpa [toAHom] using this
  · rw [natCard_torus, Nat.card_congr Additive.toMul, card_Ag]
    decide

@[expose] noncomputable def toAEquiv : Torus (Type100.k 1) ≃+ Additive ↥Ag :=
  AddEquiv.ofBijective toAHom toAHom_bijective

theorem coe_toAEquiv (x : Torus (Type100.k 1)) :
    ((Additive.toMul (toAEquiv x) : ↥Ag) : Mns) = toA x := rfl

theorem mnsUV_mem_Lg : mnsUV ∈ Lg := Subgroup.subset_closure (by simp [gensL])
theorem mnsT_mem_Lg : mnsT ∈ Lg := Subgroup.subset_closure (by simp [gensL])
theorem mnsU_mem_Lg : mnsU ∈ Lg := Subgroup.subset_closure (by simp [gensL])
theorem mnsRho_mem_Lg : mnsRho ∈ Lg := Subgroup.subset_closure (by simp [gensL])

theorem toAEquiv_symm_conjBy {g : Mns} (hg : g ∈ Subgroup.normalizer Ag)
    {φ : Torus (Type100.k 1) →+ Torus (Type100.k 1)}
    (h : ∀ x, toA (φ x) = g⁻¹ * toA x * g) (x : ↥Ag) :
    toAEquiv.symm (Additive.ofMul (conjBy hg x)) = φ (toAEquiv.symm (Additive.ofMul x)) := by
  apply toAEquiv.injective
  rw [AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_ofMul, coe_toAEquiv, h]
  have hx : ((Additive.toMul (toAEquiv (toAEquiv.symm (Additive.ofMul x))) : ↥Ag) : Mns) =
      (x : Mns) := by
    rw [AddEquiv.apply_symm_apply, toMul_ofMul]
  rw [coe_toAEquiv] at hx
  simp [conjBy, hx]

@[expose] noncomputable def mnsDataA : StrothTypeData Ag (StrothTypeIndex.t100 1) where
  e := toAEquiv.symm
  uv := mnsUV
  t := mnsT
  u := mnsU
  ρ := mnsRho
  uv_sq := by decide
  t_sq := by decide
  uv_comm_t := by decide
  rho_cube := by decide
  u_sq := by decide
  u_rho := by decide
  uv_rho := by decide
  t_rho := by decide
  uv_comm_u := by decide
  t_u := by decide
  uv_mem := Lg_le_normalizer mnsUV_mem_Lg
  t_mem := Lg_le_normalizer mnsT_mem_Lg
  u_mem := Lg_le_normalizer mnsU_mem_Lg
  ρ_mem := Lg_le_normalizer mnsRho_mem_Lg
  uv_conj := toAEquiv_symm_conjBy _ toA_uv
  t_conj := toAEquiv_symm_conjBy _ toA_t
  u_conj := toAEquiv_symm_conjBy _ toA_u
  ρ_conj := toAEquiv_symm_conjBy _ toA_rho

end MnsData

section Lift

private theorem odd_card_oddCore_frame (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore (G := X), ← CFSG.pPrimeCore_eq_piCore X 2]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

private theorem odd_orderOf_of_mem_oddCore {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ CFSG.oddCore X) : Odd (orderOf x) := by
  have h := Subgroup.orderOf_dvd_natCard (CFSG.oddCore X) hx
  exact Odd.of_dvd_nat (odd_card_oddCore_frame X) h

theorem exists_lift_Tg {H : Type*} [Group H] [Finite H]
    (e : Mns ≃* H ⧸ CFSG.oddCore H) :
    ∃ l : ↥Tg →* H, Function.Injective l ∧
      ∀ m : ↥Tg, QuotientGroup.mk' (CFSG.oddCore H) (l m) = e m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.oddCore H)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨Sg, hSg⟩ := Tg_isSylow
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hπ 2
    (Sylow.mapSurjective (f := (e : Mns →* H ⧸ CFSG.oddCore H)) e.surjective Sg)
  have hTmap : (T : Subgroup H).map (QuotientGroup.mk' (CFSG.oddCore H)) =
      Tg.map (e : Mns →* H ⧸ CFSG.oddCore H) := by
    have := congrArg (fun P : Sylow 2 (H ⧸ CFSG.oddCore H) => (P : Subgroup (H ⧸ CFSG.oddCore H)))
      hT
    simpa [Sylow.coe_mapSurjective, hSg] using this
  have hcop : Nat.Coprime (Nat.card (T : Subgroup H)) (Nat.card (CFSG.oddCore H)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.2
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_card_oddCore_frame H))
  have hinf : (T : Subgroup H) ⊓ CFSG.oddCore H = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.oddCore H)).comp (T : Subgroup H).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : (x : H) ∈ CFSG.oddCore H := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hx' : (x : H) ∈ (T : Subgroup H) ⊓ CFSG.oddCore H := ⟨x.2, hxO⟩
    rw [hinf, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  have hrange : Tg.map (e : Mns →* H ⧸ CFSG.oddCore H) =
      ((QuotientGroup.mk' (CFSG.oddCore H)).comp (T : Subgroup H).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hTmap]
  refine ⟨(T : Subgroup H).subtype.comp
    ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
      ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp (e.subgroupMap Tg).toMonoidHom)),
    ?_, ?_⟩
  · intro m m' h
    have h1 := Subtype.ext h
    have h2 := (MonoidHom.ofInjective hinj).symm.injective h1
    have h3 := (MulEquiv.subgroupCongr hrange).injective h2
    exact (e.subgroupMap Tg).injective h3
  · intro m
    have key : ((MonoidHom.ofInjective hinj ((MonoidHom.ofInjective hinj).symm
        (MulEquiv.subgroupCongr hrange ((e.subgroupMap Tg) m))) : _) : H ⧸ CFSG.oddCore H) =
        ((QuotientGroup.mk' (CFSG.oddCore H)).comp (T : Subgroup H).subtype)
          ((MonoidHom.ofInjective hinj).symm
            (MulEquiv.subgroupCongr hrange ((e.subgroupMap Tg) m))) :=
      MonoidHom.ofInjective_apply hinj
    rw [MulEquiv.apply_symm_apply] at key
    exact key.symm

end Lift

section Gens

theorem mnsX1_mem_Tg : mnsX1 ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsY1_mem_Tg : mnsY1 ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsUV_mem_Tg : mnsUV ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsT_mem_Tg : mnsT ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsX_mem_Tg : mnsX ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsY_mem_Tg : mnsY ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsU_mem_Tg : mnsU ∈ Tg := Subgroup.subset_closure (by simp [gensT])
theorem mnsW_mem_Tg : mnsW ∈ Tg := Subgroup.subset_closure (by simp [gensT])

theorem mnsX1_mem_Ag : mnsX1 ∈ Ag := Subgroup.subset_closure (by simp [gensA])
theorem mnsY1_mem_Ag : mnsY1 ∈ Ag := Subgroup.subset_closure (by simp [gensA])
theorem mnsX_mem_Ag : mnsX ∈ Ag := Subgroup.subset_closure (by simp [gensA])
theorem mnsY_mem_Ag : mnsY ∈ Ag := Subgroup.subset_closure (by simp [gensA])
theorem mnsW_mem_Ag : mnsW ∈ Ag := Subgroup.subset_closure (by simp [gensA])

theorem mnsX1_mem_Eg : mnsX1 ∈ Eg := Subgroup.subset_closure (by simp [gensE])
theorem mnsY1_mem_Eg : mnsY1 ∈ Eg := Subgroup.subset_closure (by simp [gensE])
theorem mnsUV_mem_Eg : mnsUV ∈ Eg := Subgroup.subset_closure (by simp [gensE])
theorem mnsT_mem_Eg : mnsT ∈ Eg := Subgroup.subset_closure (by simp [gensE])

theorem mem_normalizer_subgroupOf_Tg {g : Mns} (hgT : g ∈ Tg) (hg : g ∈ Subgroup.normalizer Ag) :
    (⟨g, hgT⟩ : ↥Tg) ∈ Subgroup.normalizer (Ag.subgroupOf Tg) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hg h

end Gens

section Core

theorem map_e_symm_coe {H K : Type*} [Group H] [Group K] {B : Subgroup H} {τ : StrothTypeIndex}
    (D : StrothWeakTypeData B τ) (f : H →* K) (hf : Function.Injective f) (y : Torus τ.k) :
    ((Additive.toMul ((D.map f hf).e.symm y) : B.map f) : K) =
      f ((Additive.toMul (D.e.symm y) : B) : H) := rfl

theorem mnsDataA_e_symm_coe (y : Torus (StrothTypeIndex.t100 1).k) :
    ((Additive.toMul (mnsDataA.e.symm y) : Ag) : Mns) = toA y := rfl

theorem toA_c : toA (Torus.c : Torus (Type100.k 1)) = mnsW := by decide
theorem toA_a : toA (Torus.a : Torus (Type100.k 1)) = mnsX1 * mnsX := by decide
theorem toA_b : toA (Torus.b : Torus (Type100.k 1)) = mnsY1 * mnsY := by decide

theorem isPGroup_Tg : IsPGroup 2 Tg := by
  obtain ⟨S, hS⟩ := Tg_isSylow
  exact hS ▸ S.2

theorem exists_weakDataA {H : Type*} [Group H] [Finite H] (e : Mns ≃* H ⧸ CFSG.oddCore H)
    (EH : Subgroup H) [EH.Normal] (hEH : IsPGroup 2 EH)
    (hEHmap : EH.map (QuotientGroup.mk' (CFSG.oddCore H)) =
      Qns.map (e : Mns →* H ⧸ CFSG.oddCore H)) :
    ∃ (l : ↥Tg →* H)
      (D : StrothWeakTypeData ((Ag.subgroupOf Tg).map l) (StrothTypeIndex.t100 1)),
      Function.Injective l ∧
      (∀ m : ↥Tg, QuotientGroup.mk' (CFSG.oddCore H) (l m) = e m) ∧
      (∀ m : ↥Tg, (m : Mns) ∈ Eg → l m ∈ EH) ∧
      D.uv = l ⟨mnsUV, mnsUV_mem_Tg⟩ ∧ D.t = l ⟨mnsT, mnsT_mem_Tg⟩ ∧
      D.u = l ⟨mnsU, mnsU_mem_Tg⟩ ∧
      QuotientGroup.mk' (CFSG.oddCore H) D.ρ = e mnsRho ∧
      ((D.c : _) : H) = l ⟨mnsW, mnsW_mem_Tg⟩ ∧
      ((D.a : _) : H) = l ⟨mnsX1 * mnsX, mul_mem mnsX1_mem_Tg mnsX_mem_Tg⟩ ∧
      ((D.b : _) : H) = l ⟨mnsY1 * mnsY, mul_mem mnsY1_mem_Tg mnsY_mem_Tg⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hπl⟩ := exists_lift_Tg e
  have hO := odd_card_oddCore_frame H
  have hinjl : ∀ {x y : H}, x ∈ l.range → y ∈ l.range →
      QuotientGroup.mk' (CFSG.oddCore H) x = QuotientGroup.mk' (CFSG.oddCore H) y → x = y := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩ h
    rw [hπl, hπl] at h
    exact congrArg l (Subtype.ext (e.injective h))
  have hAH_le : (Ag.subgroupOf Tg).map l ≤ l.range := Subgroup.map_le_range l _
  have hinjA : Function.Injective
      ((QuotientGroup.mk' (CFSG.oddCore H)).comp ((Ag.subgroupOf Tg).map l).subtype) :=
    fun x y h => Subtype.ext (hinjl (hAH_le x.2) (hAH_le y.2) h)
  have hπl' : (QuotientGroup.mk' (CFSG.oddCore H)).comp l =
      (e : Mns →* H ⧸ CFSG.oddCore H).comp Tg.subtype := MonoidHom.ext hπl
  have hAHmap : ((Ag.subgroupOf Tg).map l).map (QuotientGroup.mk' (CFSG.oddCore H)) =
      Ag.map (e : Mns →* H ⧸ CFSG.oddCore H) := by
    rw [Subgroup.map_map, hπl', ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left Ag_le_Tg]
  have hl3 : ∀ (a b : ↥Tg), (a : Mns) = b → l a = l b := fun a b h => congrArg l (Subtype.ext h)
  have hnormT : ∀ {g : Mns} (hgT : g ∈ Tg), g ∈ Lg →
      l ⟨g, hgT⟩ ∈ Subgroup.normalizer ((Ag.subgroupOf Tg).map l) := fun hgT hgL =>
    map_mem_normalizer_map l (mem_normalizer_subgroupOf_Tg hgT (Lg_le_normalizer hgL))
  have hT2 := isPGroup_Tg
  have hAH2 : IsPGroup 2 ((Ag.subgroupOf Tg).map l) := (hT2.to_subgroup _).map l
  have hFr := CFSG.Holt.H78.map_normalizer_eq_of_odd (CFSG.oddCore H) hO hAH2
  have hρbar : e mnsRho ∈ Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (QuotientGroup.mk' (CFSG.oddCore H)) :
        Subgroup (H ⧸ CFSG.oddCore H)) : Set (H ⧸ CFSG.oddCore H)) := by
    rw [hAHmap]
    exact map_mem_normalizer_map (e : Mns →* H ⧸ CFSG.oddCore H)
      (Lg_le_normalizer mnsRho_mem_Lg)
  rw [← hFr] at hρbar
  obtain ⟨ρ0, hρ0N, hρ0⟩ := hρbar
  obtain ⟨g, hgdef⟩ : ∃ g : H, g = l ⟨mnsU, mnsU_mem_Tg⟩ * ρ0 := ⟨_, rfl⟩
  have hgN : g ∈ Subgroup.normalizer ((Ag.subgroupOf Tg).map l) := by
    rw [hgdef]; exact mul_mem (hnormT mnsU_mem_Tg mnsU_mem_Lg) hρ0N
  have hk1 : QuotientGroup.mk' (CFSG.oddCore H) (g * g) = 1 := by
    rw [hgdef, map_mul, map_mul, hρ0, hπl]
    change e mnsU * e mnsRho * (e mnsU * e mnsRho) = 1
    rw [← map_mul, ← map_mul, show mnsU * mnsRho * (mnsU * mnsRho) = 1 by decide, map_one]
  have hkO : g * g ∈ CFSG.oddCore H := (QuotientGroup.eq_one_iff _).mp hk1
  have hkC : g * g ∈ Subgroup.centralizer (((Ag.subgroupOf Tg).map l : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hkN : g * g ∈ Subgroup.normalizer ((Ag.subgroupOf Tg).map l) := mul_mem hgN hgN
    have h1 : (g * g) * a * (g * g)⁻¹ ∈ (Ag.subgroupOf Tg).map l :=
      (Subgroup.mem_normalizer_iff.mp hkN a).mp ha
    have h2 : QuotientGroup.mk' (CFSG.oddCore H) ((g * g) * a * (g * g)⁻¹) =
        QuotientGroup.mk' (CFSG.oddCore H) a := by
      rw [map_mul, map_mul, map_inv, hk1]
      group
    have h3 := hinjl (hAH_le h1) (hAH_le ha) h2
    calc a * (g * g) = (g * g) * a * (g * g)⁻¹ * (g * g) := by rw [h3]
      _ = (g * g) * a := by group
  have hr : Odd (orderOf (g * g)) := odd_orderOf_of_mem_oddCore hkO
  obtain ⟨ρH, hρHdef⟩ : ∃ ρH : H, ρH = ρ0 * (g * g) ^ (orderOf (g * g) / 2) := ⟨_, rfl⟩
  have hgρ : l ⟨mnsU, mnsU_mem_Tg⟩ * ρH = g ^ orderOf (g * g) := by
    conv_rhs => rw [← Nat.two_mul_div_two_add_one_of_odd hr]
    rw [pow_succ', pow_mul, sq, hρHdef, ← mul_assoc, ← hgdef]
  have hu_rho : l ⟨mnsU, mnsU_mem_Tg⟩ * ρH * l ⟨mnsU, mnsU_mem_Tg⟩ * ρH = 1 := by
    rw [mul_assoc (l ⟨mnsU, mnsU_mem_Tg⟩ * ρH), hgρ, ← (Commute.refl g).mul_pow,
      pow_orderOf_eq_one]
  have hρHN : ρH ∈ Subgroup.normalizer ((Ag.subgroupOf Tg).map l) := by
    rw [hρHdef]
    exact mul_mem hρ0N (pow_mem (Subgroup.centralizer_le_normalizer _ hkC) _)
  have hπρH : QuotientGroup.mk' (CFSG.oddCore H) ρH = e mnsRho := by
    rw [hρHdef, map_mul, map_pow, hk1, one_pow, mul_one, hρ0]
  have hρodd : Odd (orderOf ρH) := by
    have h3 : ρH ^ 3 ∈ CFSG.oddCore H := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change QuotientGroup.mk' (CFSG.oddCore H) (ρH ^ 3) = 1
      rw [map_pow, hπρH, ← map_pow, show mnsRho ^ 3 = 1 by decide, map_one]
    have hdvd : orderOf ρH ∣ 3 * orderOf (ρH ^ 3) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat (Odd.mul (by decide) (odd_orderOf_of_mem_oddCore h3)) hdvd
  have hcopE : Nat.Coprime (Nat.card (EH ⊔ l.range : Subgroup H)) (Nat.card (CFSG.oddCore H)) := by
    have hp : IsPGroup 2 (EH ⊔ l.range : Subgroup H) :=
      IsPGroup.to_sup_of_normal_left hEH
        (hT2.of_surjective l.rangeRestrict l.rangeRestrict_surjective)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hO)
  have hlE : ∀ m : ↥Tg, (m : Mns) ∈ Eg → l m ∈ EH := by
    intro m hm
    have hm' : QuotientGroup.mk' (CFSG.oddCore H) (l m) ∈
        EH.map (QuotientGroup.mk' (CFSG.oddCore H)) := by
      rw [hEHmap, hπl, ← Eg_eq_Qns]
      exact ⟨m, hm, rfl⟩
    obtain ⟨ε, hε, hεm⟩ := hm'
    have h1 : ε⁻¹ * l m ∈ CFSG.oddCore H := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change QuotientGroup.mk' (CFSG.oddCore H) (ε⁻¹ * l m) = 1
      rw [map_mul, map_inv, hεm, inv_mul_cancel]
    have hε' : ε ∈ (EH ⊔ l.range : Subgroup H) := Subgroup.mem_sup_left hε
    have hm2 : l m ∈ (EH ⊔ l.range : Subgroup H) := Subgroup.mem_sup_right ⟨m, rfl⟩
    have h3 : ε⁻¹ * l m ∈ (EH ⊔ l.range : Subgroup H) ⊓ CFSG.oddCore H :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hε') hm2, h1⟩
    rw [Subgroup.inf_eq_bot_of_coprime hcopE, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3 ▸ hε
  have hcopE' : Nat.Coprime (Nat.card EH) (Nat.card (CFSG.oddCore H)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEH
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hO)
  have hinjE : ∀ {x y : H}, x ∈ EH → y ∈ EH →
      QuotientGroup.mk' (CFSG.oddCore H) x = QuotientGroup.mk' (CFSG.oddCore H) y → x = y := by
    intro x y hx hy h
    have h1 : x⁻¹ * y ∈ EH ⊓ CFSG.oddCore H := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx) hy,
      (QuotientGroup.eq (s := CFSG.oddCore H)).mp h⟩
    rw [Subgroup.inf_eq_bot_of_coprime hcopE', Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hconjE : ∀ {x : H}, x ∈ EH → ρH⁻¹ * x * ρH ∈ EH := fun hx => by
    simpa using (inferInstance : EH.Normal).conj_mem _ hx ρH⁻¹
  have huvE := hlE ⟨mnsUV, mnsUV_mem_Tg⟩ mnsUV_mem_Eg
  have htE := hlE ⟨mnsT, mnsT_mem_Tg⟩ mnsT_mem_Eg
  have huv_rho : l ⟨mnsUV, mnsUV_mem_Tg⟩ * ρH = ρH * l ⟨mnsT, mnsT_mem_Tg⟩ := by
    have h : ρH⁻¹ * l ⟨mnsUV, mnsUV_mem_Tg⟩ * ρH = l ⟨mnsT, mnsT_mem_Tg⟩ := by
      refine hinjE (hconjE huvE) htE ?_
      simp only [map_mul, map_inv, hπρH, hπl]
      change (e mnsRho)⁻¹ * e mnsUV * e mnsRho = e mnsT
      rw [← map_inv, ← map_mul, ← map_mul,
        show mnsRho⁻¹ * mnsUV * mnsRho = mnsT by decide]
    rw [← h]
    group
  have ht_rho : l ⟨mnsT, mnsT_mem_Tg⟩ * ρH =
      ρH * l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsT, mnsT_mem_Tg⟩ := by
    have h : ρH⁻¹ * l ⟨mnsT, mnsT_mem_Tg⟩ * ρH =
        l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsT, mnsT_mem_Tg⟩ := by
      refine hinjE (hconjE htE) (mul_mem huvE htE) ?_
      simp only [map_mul, map_inv, hπρH, hπl]
      change (e mnsRho)⁻¹ * e mnsT * e mnsRho = e mnsUV * e mnsT
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul,
        show mnsRho⁻¹ * mnsT * mnsRho = mnsUV * mnsT by decide]
    calc l ⟨mnsT, mnsT_mem_Tg⟩ * ρH = ρH * (ρH⁻¹ * l ⟨mnsT, mnsT_mem_Tg⟩ * ρH) := by group
      _ = _ := by rw [h, ← mul_assoc]
  have huv_sq : l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsUV, mnsUV_mem_Tg⟩ = 1 := by
    rw [← map_mul, ← map_one l]; exact hl3 _ _ (show mnsUV * mnsUV = 1 by decide)
  have ht_sq : l ⟨mnsT, mnsT_mem_Tg⟩ * l ⟨mnsT, mnsT_mem_Tg⟩ = 1 := by
    rw [← map_mul, ← map_one l]; exact hl3 _ _ (show mnsT * mnsT = 1 by decide)
  have hu_sq : l ⟨mnsU, mnsU_mem_Tg⟩ * l ⟨mnsU, mnsU_mem_Tg⟩ = 1 := by
    rw [← map_mul, ← map_one l]; exact hl3 _ _ (show mnsU * mnsU = 1 by decide)
  have huv_t : l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsT, mnsT_mem_Tg⟩ =
      l ⟨mnsT, mnsT_mem_Tg⟩ * l ⟨mnsUV, mnsUV_mem_Tg⟩ := by
    rw [← map_mul, ← map_mul]; exact hl3 _ _ (show mnsUV * mnsT = mnsT * mnsUV by decide)
  have huv_u : l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsU, mnsU_mem_Tg⟩ =
      l ⟨mnsU, mnsU_mem_Tg⟩ * l ⟨mnsUV, mnsUV_mem_Tg⟩ := by
    rw [← map_mul, ← map_mul]; exact hl3 _ _ (show mnsUV * mnsU = mnsU * mnsUV by decide)
  have ht_u : l ⟨mnsT, mnsT_mem_Tg⟩ * l ⟨mnsU, mnsU_mem_Tg⟩ =
      l ⟨mnsU, mnsU_mem_Tg⟩ * l ⟨mnsUV, mnsUV_mem_Tg⟩ * l ⟨mnsT, mnsT_mem_Tg⟩ := by
    rw [← map_mul, ← map_mul, ← map_mul]
    exact hl3 _ _ (show mnsT * mnsU = mnsU * mnsUV * mnsT by decide)
  let D' := (mnsDataA.toWeak).map (e : Mns →* H ⧸ CFSG.oddCore H) e.injective
  let D := StrothWeakTypeData.ofMap (QuotientGroup.mk' (CFSG.oddCore H)) hinjA hAHmap D'
    (hπl _) (hπl _) (hπl _) hπρH huv_sq ht_sq huv_t hρodd hu_sq hu_rho huv_rho ht_rho huv_u ht_u
    (hnormT mnsUV_mem_Tg mnsUV_mem_Lg) (hnormT mnsT_mem_Tg mnsT_mem_Lg)
    (hnormT mnsU_mem_Tg mnsU_mem_Lg) hρHN
  have hgen : ∀ (y : Torus (Type100.k 1)) {m : Mns} (hm : m ∈ Tg), toA y = m → m ∈ Ag →
      (((Additive.toMul (D.e.symm y)) : _) : H) = l ⟨m, hm⟩ := by
    intro y m hm hy hmA
    have h1 := StrothWeakTypeData.map_ofMap_e_symm (QuotientGroup.mk' (CFSG.oddCore H)) hinjA
      hAHmap D' (hπl _) (hπl _) (hπl _) hπρH huv_sq ht_sq huv_t hρodd hu_sq hu_rho huv_rho ht_rho
      huv_u ht_u (hnormT mnsUV_mem_Tg mnsUV_mem_Lg) (hnormT mnsT_mem_Tg mnsT_mem_Lg)
      (hnormT mnsU_mem_Tg mnsU_mem_Lg) hρHN y
    refine hinjl (hAH_le (Additive.toMul (D.e.symm y)).2) ⟨⟨m, hm⟩, rfl⟩ ?_
    rw [h1, hπl]
    change (e : Mns →* H ⧸ CFSG.oddCore H) (toA y) = e m
    rw [hy]
    rfl
  refine ⟨l, D, hl, hπl, hlE, rfl, rfl, rfl, hπρH, ?_, ?_, ?_⟩
  · exact hgen _ mnsW_mem_Tg toA_c mnsW_mem_Ag
  · exact hgen _ _ toA_a (mul_mem mnsX1_mem_Ag mnsX_mem_Ag)
  · exact hgen _ _ toA_b (mul_mem mnsY1_mem_Ag mnsY_mem_Ag)

end Core

section Frame

theorem Ag_le_NAg : Ag ≤ NAg := Subgroup.le_normalizer

theorem Tg_le_NAg : Tg ≤ NAg := by
  rw [Tg, Subgroup.closure_le]
  intro g hg
  simp only [gensT, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ag_le_NAg mnsX1_mem_Ag
  · exact Ag_le_NAg mnsY1_mem_Ag
  · exact Lg_le_normalizer mnsUV_mem_Lg
  · exact Lg_le_normalizer mnsT_mem_Lg
  · exact Ag_le_NAg mnsX_mem_Ag
  · exact Ag_le_NAg mnsY_mem_Ag
  · exact Lg_le_normalizer mnsU_mem_Lg
  · exact Ag_le_NAg mnsW_mem_Ag

theorem card_closure_E_Tg :
    Nat.card (Subgroup.closure ({⟨mnsX1, mnsX1_mem_Tg⟩, ⟨mnsY1, mnsY1_mem_Tg⟩,
      ⟨mnsUV, mnsUV_mem_Tg⟩, ⟨mnsT, mnsT_mem_Tg⟩} : Set ↥Tg)) = 16 := by
  rw [← Subgroup.card_map_of_injective (f := Tg.subtype) Subtype.coe_injective,
    MonoidHom.map_closure]
  have h : (Tg.subtype '' ({⟨mnsX1, mnsX1_mem_Tg⟩, ⟨mnsY1, mnsY1_mem_Tg⟩,
      ⟨mnsUV, mnsUV_mem_Tg⟩, ⟨mnsT, mnsT_mem_Tg⟩} : Set ↥Tg)) = {g | g ∈ gensE} := by
    ext g
    simp [gensE, Set.image_insert_eq]
  rw [h, ← Eg, card_Eg]

theorem exists_strothFrame_of_data {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {E : Subgroup G} (hE : IsE 4 ↥E)
    (φ : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : φ.ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)))
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E)
    (θ : (↥(Subgroup.normalizer (E : Set G)) ⧸ CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))
      →* Equiv.Perm (Fin 6)) (hθ : Function.Surjective θ)
    (hθker : θ.ker = (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
      (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))))
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ g (v : Multiplicative (altHeart 6)), g * (ψ v : _) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : _))
    (hns : ¬ ∃ K : Subgroup (↥(Subgroup.normalizer (E : Set G)) ⧸
      CFSG.oddCore ↥(Subgroup.normalizer (E : Set G))), θ.ker ⊓ K = ⊥ ∧ θ.ker ⊔ K = ⊤) :
    ∃ F : StrothFrame G, F.E = E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, -, he2⟩ := exists_mulEquiv_Mns_of_nonsplit θ hθ ψ hconj hns
  have hEle : E ≤ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer
  have hEcard : Nat.card E = 16 := by rw [hE.2]; norm_num
  have hEH : IsPGroup 2 (E.subgroupOf (Subgroup.normalizer (E : Set G))) := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, hEcard]
    norm_num
  have hEHmap : (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
      (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) =
      Qns.map (e : Mns →* _) := by
    rw [← hθker, ← map_Qns_eq_ker θ e he2]
    rfl
  obtain ⟨l, D, hl, hπl, hlE, huv, ht, hu, hρ, hc, ha, hb⟩ :=
    exists_weakDataA e (E.subgroupOf (Subgroup.normalizer (E : Set G))) hEH hEHmap
  have hinjN : Function.Injective (Subgroup.normalizer (E : Set G)).subtype :=
    Subtype.coe_injective
  obtain ⟨ψl, hψl⟩ : ∃ f : ↥Tg →* G, f = (Subgroup.normalizer (E : Set G)).subtype.comp l :=
    ⟨_, rfl⟩
  have hψapp : ∀ m, ψl m = ((l m : ↥(Subgroup.normalizer (E : Set G))) : G) := fun m => by
    rw [hψl]; rfl
  have hψinj : Function.Injective ψl := by rw [hψl]; exact hinjN.comp hl
  let dA := D.map (Subgroup.normalizer (E : Set G)).subtype hinjN
  have hP2 : IsPGroup 2 ψl.range :=
    isPGroup_Tg.of_surjective ψl.rangeRestrict ψl.rangeRestrict_surjective
  have hPN : ψl.range ≤ Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G) := by
    rintro _ ⟨m, rfl⟩
    have h1 : m ∈ Subgroup.normalizer (Ag.subgroupOf Tg) :=
      mem_normalizer_subgroupOf_Tg m.2 (Tg_le_NAg m.2)
    have h2 := map_mem_normalizer_map l h1
    have h3 := map_mem_normalizer_map (Subgroup.normalizer (E : Set G)).subtype h2
    rw [hψapp]
    exact h3
  have hAP : ((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype ≤
      ψl.range := by
    rintro _ ⟨_, ⟨m, -, rfl⟩, rfl⟩
    exact ⟨m, hψapp m⟩
  have hP' : IsPGroup 2 (ψl.range.subgroupOf (Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G))) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQ2 := Q.2.map (Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G)).subtype
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hPS : ψl.range ≤ (S : Subgroup G) := by
    intro x hx
    exact hS ⟨⟨x, hPN hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hnsyl : IsSylowIn 2 (Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G))
      ((S : Subgroup G) ⊓ Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G)) := by
    refine ⟨inf_le_right, S.2.to_le inf_le_left, ?_⟩
    intro h2
    have hle : (Q : Subgroup _).map (Subgroup.normalizer
        ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
          Subgroup G) : Set G)).subtype ≤ (S : Subgroup G) ⊓ Subgroup.normalizer
        ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
          Subgroup G) : Set G) :=
      le_inf hS (Subgroup.map_subtype_le _)
    have hdvd := Subgroup.relIndex_dvd_of_le_left (L := Subgroup.normalizer
      ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
        Subgroup G) : Set G)) hle
    have hsub : ((Q : Subgroup _).map (Subgroup.normalizer
        ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
          Subgroup G) : Set G)).subtype).subgroupOf (Subgroup.normalizer
        ((((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype :
          Subgroup G) : Set G)) = Q := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [Subtype.coe_injective hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [Subgroup.relIndex, Subgroup.relIndex, hsub] at hdvd
    exact Q.not_dvd_index (h2.trans hdvd)
  have hdAuv : dA.uv = ψl ⟨mnsUV, mnsUV_mem_Tg⟩ := by
    rw [hψapp, ← huv]; rfl
  have hdAt : dA.t = ψl ⟨mnsT, mnsT_mem_Tg⟩ := by
    rw [hψapp, ← ht]; rfl
  have hdAu : dA.u = ψl ⟨mnsU, mnsU_mem_Tg⟩ := by
    rw [hψapp, ← hu]; rfl
  have hdAc : ((dA.c : _) : G) = (((D.c : _) : ↥(Subgroup.normalizer (E : Set G))) : G) := rfl
  have hdAa : ((dA.a : _) : G) = ψl ⟨mnsX1 * mnsX, mul_mem mnsX1_mem_Tg mnsX_mem_Tg⟩ := by
    rw [hψapp, ← ha]; rfl
  have hdAb : ((dA.b : _) : G) = ψl ⟨mnsY1 * mnsY, mul_mem mnsY1_mem_Tg mnsY_mem_Tg⟩ := by
    rw [hψapp, ← hb]; rfl
  have hψ3 : ∀ (a b : ↥Tg), (a : Mns) = b → ψl a = ψl b := fun a b h =>
    congrArg ψl (Subtype.ext h)
  have hdAa2 : ((dA.a : _) : G) ^ 2 = ψl ⟨mnsX1, mnsX1_mem_Tg⟩ := by
    rw [hdAa, ← map_pow]; exact hψ3 _ _ (show (mnsX1 * mnsX) ^ 2 = mnsX1 by decide)
  have hdAb2 : ((dA.b : _) : G) ^ 2 = ψl ⟨mnsY1, mnsY1_mem_Tg⟩ := by
    rw [hdAb, ← map_pow]; exact hψ3 _ _ (show (mnsY1 * mnsY) ^ 2 = mnsY1 by decide)
  have hEeq : E = Subgroup.closure {((dA.a : _) : G) ^ 2, ((dA.b : _) : G) ^ 2, dA.uv, dA.t} := by
    rw [hdAa2, hdAb2, hdAuv, hdAt]
    have hset : ({ψl ⟨mnsX1, mnsX1_mem_Tg⟩, ψl ⟨mnsY1, mnsY1_mem_Tg⟩, ψl ⟨mnsUV, mnsUV_mem_Tg⟩,
        ψl ⟨mnsT, mnsT_mem_Tg⟩} : Set G) = ψl '' ({⟨mnsX1, mnsX1_mem_Tg⟩, ⟨mnsY1, mnsY1_mem_Tg⟩,
          ⟨mnsUV, mnsUV_mem_Tg⟩, ⟨mnsT, mnsT_mem_Tg⟩} : Set ↥Tg) := by
      simp [Set.image_insert_eq]
    have hmem : ∀ m : ↥Tg, (m : Mns) ∈ Eg → ψl m ∈ E := fun m hm => by
      rw [hψapp]; exact Subgroup.mem_subgroupOf.1 (hlE m hm)
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hmem _ mnsX1_mem_Eg
      · exact hmem _ mnsY1_mem_Eg
      · exact hmem _ mnsUV_mem_Eg
      · exact hmem _ mnsT_mem_Eg
    · rw [hset, ← MonoidHom.map_closure, Subgroup.card_map_of_injective hψinj,
        card_closure_E_Tg, hEcard]
  have hLle : dA.L ≤ Subgroup.normalizer (E : Set G) := by
    rw [StrothWeakTypeData.L, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (D.uv : ↥(Subgroup.normalizer (E : Set G))).2
    · exact (D.t : ↥(Subgroup.normalizer (E : Set G))).2
    · exact (D.u : ↥(Subgroup.normalizer (E : Set G))).2
    · exact (D.ρ : ↥(Subgroup.normalizer (E : Set G))).2
  have hAle : ((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype ≤
      Subgroup.normalizer (E : Set G) := Subgroup.map_subtype_le _
  have hmodel : ∃ φ' : ↥(Subgroup.normalizer (E : Set G)) →* Mns, Function.Surjective φ' ∧
      φ'.ker = CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)) ∧
      φ' ⟨dA.uv, hLle dA.uv_mem_L⟩ = mnsUV ∧ φ' ⟨dA.t, hLle dA.t_mem_L⟩ = mnsT ∧
      φ' ⟨dA.u, hLle dA.u_mem_L⟩ = mnsU ∧ φ' ⟨dA.ρ, hLle dA.ρ_mem_L⟩ = mnsRho ∧
      φ' ⟨(dA.c : G), hAle dA.c.2⟩ = mnsW ∧ φ' ⟨(dA.a : G), hAle dA.a.2⟩ = mnsX1 * mnsX ∧
      φ' ⟨(dA.b : G), hAle dA.b.2⟩ = mnsY1 * mnsY := by
    refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    · ext x
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    · change e.symm (QuotientGroup.mk' _ D.uv) = _
      rw [huv, hπl, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ D.t) = _
      rw [ht, hπl, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ D.u) = _
      rw [hu, hπl, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ D.ρ) = _
      rw [hρ, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ ((D.c : _) : ↥(Subgroup.normalizer (E : Set G)))) = _
      rw [hc, hπl, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ ((D.a : _) : ↥(Subgroup.normalizer (E : Set G)))) = _
      rw [ha, hπl, MulEquiv.symm_apply_apply]
    · change e.symm (QuotientGroup.mk' _ ((D.b : _) : ↥(Subgroup.normalizer (E : Set G)))) = _
      rw [hb, hπl, MulEquiv.symm_apply_apply]
  exact ⟨{ simple := hG
           S := S
           A := ((Ag.subgroupOf Tg).map l).map (Subgroup.normalizer (E : Set G)).subtype
           dA := dA
           E := E
           E_eq := hEeq
           E_isE := hE
           E_quot := ⟨φ, hφ, hker⟩
           E_syl := hsyl
           A_le_S := hAP.trans hPS
           uv_mem_S := hPS (by rw [hdAuv]; exact ⟨_, rfl⟩)
           t_mem_S := hPS (by rw [hdAt]; exact ⟨_, rfl⟩)
           u_mem_S := hPS (by rw [hdAu]; exact ⟨_, rfl⟩)
           nsylowA := hnsyl
           L_le := hLle
           A_le := hAle
           model := hmodel }, rfl⟩

theorem exists_strothFrame {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {E : Subgroup G} (hE : IsE 4 ↥E)
    (φ : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : φ.ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)))
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E)
    (hns : ¬ ∃ K : Subgroup (↥(Subgroup.normalizer (E : Set G)) ⧸
      CFSG.oddCore ↥(Subgroup.normalizer (E : Set G))),
      (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) ⊓ K = ⊥ ∧
      (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) ⊔ K = ⊤) :
    ∃ F : StrothFrame G, F.E = E := by
  obtain ⟨-, θ, hθ, hθker, ψ, hψ⟩ := stroth10_holds hE φ hφ hker hsyl
  exact exists_strothFrame_of_data hG hE φ hφ hker hsyl θ hθ hθker ψ hψ (by rwa [hθker])

end Frame

end CFSG.CGT.Stroth77
