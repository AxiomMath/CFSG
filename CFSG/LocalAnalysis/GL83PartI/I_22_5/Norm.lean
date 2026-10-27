module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Family

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] (p : ℕ)

@[expose] def cjEmb (K : Subgroup G) (b : G) (i : ZMod p) : K →* G :=
  (MulAut.conj (b ^ i.val)).toMonoidHom.comp K.subtype

theorem cjEmb_apply (K : Subgroup G) (b : G) (i : ZMod p) (x : K) :
    cjEmb p K b i x = b ^ i.val * x * (b ^ i.val)⁻¹ := rfl

@[expose, reducible] def NormComm (K : Subgroup G) (b : G) : Prop :=
  Pairwise fun i j : ZMod p => ∀ x y : K, Commute (cjEmb p K b i x) (cjEmb p K b j y)

variable {p} [Fact p.Prime]

@[expose] def normPi {K : Subgroup G} {b : G} (hc : NormComm p K b) : (ZMod p → K) →* G :=
  MonoidHom.noncommPiCoprod (cjEmb p K b) hc

@[expose] def normHom {K : Subgroup G} {b : G} (hc : NormComm p K b) : K →* G :=
  (normPi hc).comp (MonoidHom.pi fun _ => MonoidHom.id K)

@[expose] def normSub {K : Subgroup G} {b : G} (hc : NormComm p K b) : Subgroup G :=
  (normHom hc).range

theorem normHom_apply {K : Subgroup G} {b : G} (hc : NormComm p K b) (x : K) :
    normHom hc x = normPi hc (fun _ => x) := rfl

theorem normPi_apply {K : Subgroup G} {b : G} (hc : NormComm p K b) (f : ZMod p → K) :
    normPi hc f = Finset.univ.noncommProd (fun i => cjEmb p K b i (f i))
      (fun i _ j _ h => hc h (f i) (f j)) :=
  MonoidHom.noncommPiCoprod_apply (cjEmb p K b) f

theorem normPi_mulSingle {K : Subgroup G} {b : G} (hc : NormComm p K b) (i : ZMod p) (y : K) :
    normPi hc (Pi.mulSingle i y) = b ^ i.val * y * (b ^ i.val)⁻¹ :=
  MonoidHom.noncommPiCoprod_mulSingle (cjEmb p K b) i y

theorem normSub_le_range {K : Subgroup G} {b : G} (hc : NormComm p K b) :
    normSub hc ≤ (normPi hc).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨fun _ => x, rfl⟩

@[expose] def shiftHom (K : Type*) [Group K] : (ZMod p → K) →* (ZMod p → K) :=
  MonoidHom.pi fun i => Pi.evalMonoidHom (fun _ => K) (i - 1)

theorem shiftHom_apply {K : Type*} [Group K] (f : ZMod p → K) (i : ZMod p) :
    shiftHom (p := p) K f i = f (i - 1) := rfl

theorem shiftHom_mulSingle {K : Type*} [Group K] (i : ZMod p) (y : K) :
    shiftHom (p := p) K (Pi.mulSingle i y) = Pi.mulSingle (i + 1) y := by
  funext j
  simp only [shiftHom_apply, Pi.mulSingle_apply, sub_eq_iff_eq_add]

theorem pow_val_succ {b : G} (hb : b ^ p = 1) (i : ZMod p) :
    b ^ (i + 1).val = b * b ^ i.val := by
  have h1 : (i + 1).val = (i.val + 1) % p := by
    rw [ZMod.val_add, ZMod.val_one]
  rw [h1, ← pow_eq_pow_mod _ hb, pow_succ']

theorem normPi_shift {K : Subgroup G} {b : G} (hc : NormComm p K b) (hb : b ^ p = 1)
    (f : ZMod p → K) : b * normPi hc f * b⁻¹ = normPi hc (shiftHom K f) := by
  have key : (MulAut.conj b).toMonoidHom.comp (normPi hc) = (normPi hc).comp (shiftHom K) := by
    refine MonoidHom.pi_ext fun i y => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, shiftHom_mulSingle, normPi_mulSingle]
    show b * (b ^ i.val * y * (b ^ i.val)⁻¹) * b⁻¹ = _
    rw [pow_val_succ hb]
    group
  exact DFunLike.congr_fun key f

theorem normHom_fixed {K : Subgroup G} {b : G} (hc : NormComm p K b) (hb : b ^ p = 1) (x : K) :
    b * normHom hc x * b⁻¹ = normHom hc x := by
  rw [normHom_apply, normPi_shift hc hb]
  rfl

theorem mem_normSub_comm {K : Subgroup G} {b : G} (hc : NormComm p K b) (hb : b ^ p = 1) {z : G}
    (hz : z ∈ normSub hc) : b * z = z * b := by
  obtain ⟨x, rfl⟩ := hz
  have := normHom_fixed hc hb x
  calc b * normHom hc x = b * normHom hc x * b⁻¹ * b := by group
    _ = normHom hc x * b := by rw [this]

theorem cjEmb_zero (K : Subgroup G) (b : G) (x : K) : cjEmb p K b 0 x = x := by
  simp [cjEmb_apply]

theorem normPi_mem_centralizer {K : Subgroup G} {b : G} (hc : NormComm p K b) (f : ZMod p → K)
    (hf : f 0 = 1) : normPi hc f ∈ Subgroup.centralizer (K : Set G) := by
  rw [normPi, MonoidHom.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  by_cases hi : i = 0
  · subst hi
    rw [hf, map_one]
    simp
  · have := hc (Ne.symm hi) ⟨y, hy⟩ (f i)
    rw [cjEmb_zero] at this
    exact this.eq

theorem normHom_decomp {K : Subgroup G} {b : G} (hc : NormComm p K b) (x : K) :
    ∃ d ∈ Subgroup.centralizer (K : Set G), normHom hc x = (x : G) * d := by
  classical
  let f : ZMod p → K := fun _ => x
  let f' : ZMod p → K := Function.update f 0 1
  have hf : f = Pi.mulSingle 0 x * f' := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [f', f]
    · simp [f', f, hi]
  refine ⟨normPi hc f', normPi_mem_centralizer hc f' (by simp [f']), ?_⟩
  rw [normHom_apply]
  change normPi hc f = _
  rw [hf, map_mul, normPi_mulSingle]
  simp

theorem normPi_mem_iSup_ne {K : Subgroup G} {b : G} (hc : NormComm p K b) (f : ZMod p → K)
    (hf : f 0 = 1) :
    normPi hc f ∈ ⨆ i : {i : ZMod p // i ≠ 0}, cj (b ^ i.1.val) K := by
  rw [normPi, MonoidHom.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    rw [hf, map_one]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_iSup_of_mem ⟨i, hi⟩ (mul_mem_cj (f i).2)

theorem normHom_decomp' {K : Subgroup G} {b : G} (hc : NormComm p K b) (x : K) :
    ∃ d ∈ Subgroup.centralizer (K : Set G),
      d ∈ (⨆ i : {i : ZMod p // i ≠ 0}, cj (b ^ i.1.val) K) ∧ normHom hc x = (x : G) * d := by
  classical
  let f : ZMod p → K := fun _ => x
  let f' : ZMod p → K := Function.update f 0 1
  have hf : f = Pi.mulSingle 0 x * f' := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [f', f]
    · simp [f', f, hi]
  refine ⟨normPi hc f', normPi_mem_centralizer hc f' (by simp [f']),
    normPi_mem_iSup_ne hc f' (by simp [f']), ?_⟩
  rw [normHom_apply]
  change normPi hc f = _
  rw [hf, map_mul, normPi_mulSingle]
  simp

theorem normHom_ker_le_center {K : Subgroup G} {b : G} (hc : NormComm p K b) :
    (normHom hc).ker ≤ Subgroup.center K := by
  intro x hx
  obtain ⟨d, hd, hxd⟩ := normHom_decomp hc x
  have h1 : (x : G) * d = 1 := by rw [← hxd]; exact hx
  have hx' : (x : G) = d⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  show (y : G) * x = x * y
  rw [hx']
  exact Subgroup.mem_centralizer_iff.1 (inv_mem hd) y y.2

theorem isQuasisimple_normSub {K : Subgroup G} {b : G} (hc : NormComm p K b)
    (hK : IsQuasisimple K) : IsQuasisimple (normSub hc) := by
  refine CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hK (normHom hc) ?_
  intro htop
  obtain ⟨x, y, hxy⟩ := quasisimple_nonabelian hK
  have hx : x ∈ Subgroup.center K := normHom_ker_le_center hc (htop ▸ Subgroup.mem_top x)
  exact hxy (Subgroup.mem_center_iff.1 hx y).symm

@[expose] def cjHom (c : G) (K : Subgroup G) : K →* cj c K :=
  (MulAut.conj c).toMonoidHom.subgroupMap K

theorem cjHom_surjective (c : G) (K : Subgroup G) : Function.Surjective (cjHom c K) :=
  MonoidHom.subgroupMap_surjective _ K

theorem coe_cjHom (c : G) (K : Subgroup G) (x : K) : (cjHom c K x : G) = c * x * c⁻¹ := rfl

omit [Fact p.Prime] in
theorem cjEmb_cj {K : Subgroup G} {b c : G} (hcb : c * b = b * c) (i : ZMod p) (x : K) :
    cjEmb p (cj c K) b i (cjHom c K x) = c * cjEmb p K b i x * c⁻¹ := by
  rw [cjEmb_apply, cjEmb_apply, coe_cjHom]
  have hcu : Commute c (b ^ i.val) := Commute.pow_right hcb i.val
  calc b ^ i.val * (c * x * c⁻¹) * (b ^ i.val)⁻¹
      = (b ^ i.val * c) * x * (c⁻¹ * (b ^ i.val)⁻¹) := by group
    _ = (c * b ^ i.val) * x * ((b ^ i.val)⁻¹ * c⁻¹) := by
        rw [← hcu.eq, hcu.inv_inv.eq]
    _ = c * (b ^ i.val * x * (b ^ i.val)⁻¹) * c⁻¹ := by group

omit [Fact p.Prime] in
theorem NormComm.cj' {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hcb : c * b = b * c) :
    NormComm p (cj c K) b := by
  intro i j hij x y
  obtain ⟨x', hx'⟩ := (cjHom_surjective c K) x
  obtain ⟨y', hy'⟩ := (cjHom_surjective c K) y
  subst hx' hy'
  rw [cjEmb_cj hcb, cjEmb_cj hcb]
  exact (hc hij x' y').map (MulAut.conj c).toMonoidHom

theorem normHom_cj {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hc' : NormComm p (cj c K) b)
    (hcb : c * b = b * c) (x : K) :
    normHom hc' (cjHom c K x) = c * normHom hc x * c⁻¹ := by
  let Φ : (ZMod p → K) →* (ZMod p → cj c K) :=
    MonoidHom.pi fun i => (cjHom c K).comp (Pi.evalMonoidHom (fun _ => K) i)
  have key : (normPi hc').comp Φ = (MulAut.conj c).toMonoidHom.comp (normPi hc) := by
    refine MonoidHom.pi_ext fun i y => ?_
    have hΦ : Φ (Pi.mulSingle i y) = Pi.mulSingle i (cjHom c K y) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [Φ]
      · simp [Φ, hj]
    simp only [MonoidHom.coe_comp, Function.comp_apply, hΦ, normPi_mulSingle]
    rw [← cjEmb_apply, ← cjEmb_apply, cjEmb_cj hcb]
    rfl
  have h1 := DFunLike.congr_fun key (fun _ => x)
  have hdiag : Φ (fun _ => x) = fun _ => cjHom c K x := rfl
  simp only [MonoidHom.coe_comp, Function.comp_apply, hdiag] at h1
  rw [normHom_apply, normHom_apply]
  exact h1

theorem normSub_cj {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hc' : NormComm p (cj c K) b)
    (hcb : c * b = b * c) : normSub hc' = cj c (normSub hc) := by
  ext z
  constructor
  · rintro ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := cjHom_surjective c K x'
    rw [normHom_cj hc hc' hcb, mem_cj]
    have : c⁻¹ * (c * normHom hc x * c⁻¹) * c = normHom hc x := by group
    rw [this]
    exact ⟨x, rfl⟩
  · intro hz
    rw [mem_cj] at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨cjHom c K x, ?_⟩
    rw [normHom_cj hc hc' hcb, hx]
    group

theorem commute_normPi {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hcb : c * b = b * c)
    (hcK : ∀ x ∈ K, c * x = x * c) (f : ZMod p → K) : Commute c (normPi hc f) := by
  refine MonoidHom.commute_noncommPiCoprod (cjEmb p K b) (m := c) (fun i y => ?_) f
  rw [cjEmb_apply]
  have hcu : Commute c (b ^ i.val) := Commute.pow_right hcb i.val
  have hcy : Commute c y := hcK y y.2
  exact (hcu.mul_right hcy).mul_right hcu.inv_right

theorem commute_normSub {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hcb : c * b = b * c)
    (hcK : ∀ x ∈ K, c * x = x * c) {z : G} (hz : z ∈ normSub hc) : c * z = z * c := by
  obtain ⟨x, rfl⟩ := hz
  exact commute_normPi hc hcb hcK (fun _ => x)

section FamNorm

variable {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.orderOf_eq (hF : IsFam p B 𝒦) {b : G} (hb : b ∈ B) {A : Subgroup G}
    (hbA : b ∉ A) : orderOf b = p :=
  orderOf_eq_prime (hF.elem.2 b hb) (fun h => hbA (h ▸ A.one_mem))

theorem inv_pow_mul_pow_eq_zpow (b : G) (m n : ℕ) :
    (b ^ m)⁻¹ * b ^ n = b ^ ((n : ℤ) - m) := by
  rw [zpow_sub, zpow_natCast, zpow_natCast]
  exact ((Commute.pow_pow_self b m n).inv_left).eq

theorem IsFam.cj_pow_ne (hF : IsFam p B 𝒦) {K : Subgroup G} {b : G} (hb : b ∈ B)
    (hbA : b ∉ stab B K) {i j : ZMod p} (hij : i ≠ j) :
    cj (b ^ i.val) K ≠ cj (b ^ j.val) K := by
  intro h
  have h1 : cj ((b ^ i.val)⁻¹ * b ^ j.val) K = K := by
    rw [cj_mul, ← h, cj_inv_cj]
  have hmem : (b ^ i.val)⁻¹ * b ^ j.val ∈ stab B K :=
    mem_stab.2 ⟨B.mul_mem (B.inv_mem (B.pow_mem hb _)) (B.pow_mem hb _), h1⟩
  rw [inv_pow_mul_pow_eq_zpow] at hmem
  have hord := hF.orderOf_eq hb hbA
  have hdvd := (zpow_mem_iff_dvd hord hbA _).1 hmem
  apply hij
  have h2 : (((j.val : ℤ) - i.val : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
  push_cast at h2
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
  exact (sub_eq_zero.1 h2).symm

theorem IsFam.normComm (hF : IsFam p B 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {b : G} (hb : b ∈ B)
    (hbA : b ∉ stab B K) : NormComm p K b := by
  intro i j hij x y
  have hi : cj (b ^ i.val) K ∈ 𝒦 := hF.smul_mem K hK _ (B.pow_mem hb _)
  have hj : cj (b ^ j.val) K ∈ 𝒦 := hF.smul_mem K hK _ (B.pow_mem hb _)
  exact hF.comm _ hi _ hj (hF.cj_pow_ne hb hbA hij) (cjEmb p K b i x) (mul_mem_cj x.2)
    (cjEmb p K b j y) (mul_mem_cj y.2)

omit [Fact p.Prime] in
theorem IsFam.not_mem_stab (hF : IsFam p B 𝒦) {K₀ K : Subgroup G} (hK₀ : K₀ ∈ 𝒦) (hK : K ∈ 𝒦)
    {b : G} (hbA : b ∉ stab B K₀) : b ∉ stab B K := by
  rw [hF.stab_eq hK hK₀]
  exact hbA

@[expose] def normFam (hF : IsFam p B 𝒦) (b : G) (hb : b ∈ B) : Set (Subgroup G) :=
  {M | ∃ K, ∃ hK : K ∈ 𝒦, ∃ hbA : b ∉ stab B K, M = normSub (hF.normComm hK hb hbA)}

theorem normSub_mem_normFam (hF : IsFam p B 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {b : G} (hb : b ∈ B)
    (hbA : b ∉ stab B K) : normSub (hF.normComm hK hb hbA) ∈ normFam hF b hb :=
  ⟨K, hK, hbA, rfl⟩

theorem normSub_le_iSup {K : Subgroup G} {b : G} (hc : NormComm p K b) :
    normSub hc ≤ ⨆ i : ZMod p, cj (b ^ i.val) K := by
  refine (normSub_le_range hc).trans ?_
  rw [normPi, MonoidHom.noncommPiCoprod_range]
  refine iSup_mono fun _ => ?_
  rintro _ ⟨x, rfl⟩
  exact mul_mem_cj x.2

theorem normSub_le_layer (hF : IsFam p B 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {b : G} (hb : b ∈ B)
    (hc : NormComm p K b) : normSub hc ≤ layer 𝒦 :=
  (normSub_le_iSup hc).trans (iSup_le fun _ =>
    le_layer (hF.smul_mem K hK _ (B.pow_mem hb _)))

theorem IsFam.normSub_conj (hF : IsFam p B 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {b c : G}
    (hb : b ∈ B) (hc : c ∈ B) (hbA : b ∉ stab B K) (hbA' : b ∉ stab B (cj c K)) :
    normSub (hF.normComm (hF.smul_mem K hK c hc) hb hbA') =
      cj c (normSub (hF.normComm hK hb hbA)) :=
  normSub_cj _ _ (hF.mul_comm_of_mem hc hb)

theorem IsFam.normSub_zpow (hF : IsFam p B 𝒦) {K : Subgroup G} (hK : K ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K) (n : ℤ) (hbA' : b ∉ stab B (cj (b ^ n) K)) :
    normSub (hF.normComm (hF.smul_mem K hK (b ^ n) (B.zpow_mem hb n)) hb hbA') =
      normSub (hF.normComm hK hb hbA) := by
  rw [hF.normSub_conj hK hb (B.zpow_mem hb n) hbA hbA']
  refine cj_eq_of_comm fun z hz => ?_
  have h := mem_normSub_comm (hF.normComm hK hb hbA) (hF.elem.2 b hb) hz
  exact ((Commute.zpow_left (show Commute b z from h) n)).eq

theorem IsFam.normSub_comm (hF : IsFam p B 𝒦) {K K' : Subgroup G} (hK : K ∈ 𝒦) (hK' : K' ∈ 𝒦)
    {b : G} (hb : b ∈ B) (hbA : b ∉ stab B K) (hbA' : b ∉ stab B K')
    (hne : ∀ i j : ZMod p, cj (b ^ i.val) K ≠ cj (b ^ j.val) K') :
    ∀ z ∈ normSub (hF.normComm hK hb hbA), ∀ z' ∈ normSub (hF.normComm hK' hb hbA'),
      z * z' = z' * z := by
  intro z hz z' hz'
  refine comm_of_iSup (fun i : ZMod p => cj (b ^ i.val) K) (fun j : ZMod p => cj (b ^ j.val) K')
    ?_ z (normSub_le_iSup _ hz) z' (normSub_le_iSup _ hz')
  intro i j x hx y hy
  exact hF.comm _ (hF.smul_mem K hK _ (B.pow_mem hb _)) _
    (hF.smul_mem K' hK' _ (B.pow_mem hb _)) (hne i j) x hx y hy

end FamNorm

end GL83.CompFam
