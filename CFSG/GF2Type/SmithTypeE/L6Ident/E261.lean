module

public import CFSG.GF2Type.SmithTypeE.L6Ident.Ident
public import CFSG.GF2Type.SmithTypeE.L6Ident.Simple
public import CFSG.GF2Type.SmithTypeE.L6Ident.Lift
public import CFSG.GF2Type.SmithTypeE.L6.E23Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.GF2Type.SmithTypeE.L6
  CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithL6 (wt tvCols)
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_apply)
open scoped MatrixGroups

theorem decode_code' (v : V) : decode (SMG.code v) = v := by
  funext m
  rw [decode_apply, SMG.testBit_code]
  simp only [m.2, ↓reduceDIte]
  generalize v m = a
  revert a
  decide

theorem code_decode' {c : Nat} (hc : c < 2 ^ 20) : SMG.code (decode c) = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [SMG.testBit_code]
  split_ifs with hi
  · rw [decode_apply]
    cases c.testBit i <;> rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem applyCols_tvCols_lt' {k : Nat} (hk : k < 1953)
    (c : Nat) : applyCols (tvCols k) c < 2 ^ 20 :=
  SMG.applyCols_lt (fun m hm => (tvInv_parts hk m (by
    simpa [CFSG.SmithL6.tvCols] using hm)).1) c

theorem code_tvEquiv {k : Nat} (hk : k < 1953) (v : V) :
    SMG.code (tvEquiv k v) = applyCols (tvCols k) (SMG.code v) := by
  conv_lhs => rw [← decode_code' v]
  rw [tvEquiv_decode hk, code_decode' (applyCols_tvCols_lt' hk _)]

section E261

attribute [local irreducible] tvP T6 CFSG.SmithL6.tvList CFSG.SmithL6.tvCols CFSG.SmithL6.wt


variable {G : Type} [Group G] [Finite G]

theorem acts_of_compat {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)}
    {ψ : Mbar0 S ≃* ↥T6}
    (hcomp : ∀ (c : G) (hc : c ∈ S.M)
      (h0 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S) (u : G), u ∈ S.QG →
        φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0⟩) (φ (S.cl u)))
    {c : G} (hc : c ∈ S.M) (h0 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S)
    {k : Fin 1953} (hψ : ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩) :
    SMG.Acts S φ c (applyCols (tvCols k)) := by
  intro u hu
  rw [hcomp c hc h0 u hu, hψ, rhoMod_tvP, code_tvEquiv k.2]

theorem inv_mul_mem_QG_of_ρ_eq (S : Setting G) {a b : S.M} (h : S.ρ a = S.ρ b) :
    (a : G)⁻¹ * b ∈ S.QG := by
  have h1 : S.ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  exact (S.ρ_eq_one_iff (a⁻¹ * b)).mp h1

theorem ρ_eq_of_inv_mul_mem_QG (S : Setting G) {a b : S.M} (h : (a : G)⁻¹ * b ∈ S.QG) :
    S.ρ a = S.ρ b := by
  have h1 := (S.ρ_eq_one_iff (a⁻¹ * b)).mpr h
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

omit
  [Finite G] in
theorem commute_conj_inv {x y : G} (h : G) (hxy : Commute x y) :
    Commute (h⁻¹ * x * h) (h⁻¹ * y * h) := by
  simp only [Commute, SemiconjBy] at hxy ⊢
  calc h⁻¹ * x * h * (h⁻¹ * y * h) = h⁻¹ * (x * y) * h := by group
    _ = h⁻¹ * (y * x) * h := by rw [hxy]
    _ = h⁻¹ * y * h * (h⁻¹ * x * h) := by group

theorem exists_conj_eq_mul_of_mem_Qa (hE : SmithL6E23a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {t u h a : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htu : orderOf (t * u) = 3)
    (hbt : Commute (h * S.z * h⁻¹) t) (hbu : Commute (h * S.z * h⁻¹) u) (ha : IsConj S.z a)
    (haQ : h⁻¹ * a * h ∈ S.QG) (hab : a ≠ h * S.z * h⁻¹) (hat : Commute a t)
    (hau : Commute a u) :
    ∃ q : G, Commute q t ∧ Commute q u ∧ q * (h * S.z * h⁻¹) * q⁻¹ = h * S.z * h⁻¹ * a := by
  have ht' : IsConj S.z (h⁻¹ * t * h) := ht.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have hu' : IsConj S.z (h⁻¹ * u * h) := hu.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have ha' : IsConj S.z (h⁻¹ * a * h) := ha.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have htu' : orderOf ((h⁻¹ * t * h) * (h⁻¹ * u * h)) = 3 := by
    rw [show (h⁻¹ * t * h) * (h⁻¹ * u * h) = MulAut.conj h⁻¹ (t * u) by
      simp [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  have haz : h⁻¹ * a * h ≠ S.z := fun e => hab (by
    calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
      _ = h * S.z * h⁻¹ := by rw [e])
  obtain ⟨q, hqt, hqu, hq⟩ := exists_conj_eq_z_mul hE S hw hU ht' hu'
    (conj_inv_mem_M_of_commute S hbt) (conj_inv_mem_M_of_commute S hbu) htu' ha' haQ haz
    (commute_conj_inv h hat) (commute_conj_inv h hau)
  refine ⟨h * q * h⁻¹, ?_, ?_, ?_⟩
  · have := commute_conj_inv h⁻¹ hqt
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * t * h) * h⁻¹ = t by group] at this
  · have := commute_conj_inv h⁻¹ hqu
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * u * h) * h⁻¹ = u by group] at this
  · calc h * q * h⁻¹ * (h * S.z * h⁻¹) * (h * q * h⁻¹)⁻¹ = h * (q * S.z * q⁻¹) * h⁻¹ := by group
      _ = h * (S.z * (h⁻¹ * a * h)) * h⁻¹ := by rw [hq]
      _ = h * S.z * h⁻¹ * a := by group

theorem mem_of_acts (h34a : SmithL6E34a) (h34b : SmithL6E34b) (hE : SmithL6E23a)
    (h33 : SmithL6E33) (hF : E23FourFacts) (hwt : ∀ i < 1395, wt i ≠ 0) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)} (h1235 : SmithL6Clauses1235 S φ)
    {K : Subgroup G} (hQK : S.QG ⊓ cent2 t u ≤ K)
    (hnK : ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {y : G} (hyD : IsConj S.z y) (hyM : y ∈ S.M) (hyQ : y ∉ S.QG) (hyt : Commute y t)
    (hyu : Commute y u) {k kt ku : Nat} (hk : k < 1953)
    (hAy : SMG.Acts S φ y (applyCols (tvCols k))) (hAt : SMG.Acts S φ t (applyCols (tvCols kt)))
    (hAu : SMG.Acts S φ u (applyCols (tvCols ku)))
    (hF3 : ∃ i < 1395, InE k i ∧ applyCols (tvCols kt) (wt i) = wt i ∧
      applyCols (tvCols ku) (wt i) = wt i) : y ∈ K := by
  obtain ⟨i, hi, hEi, hfixt, hfixu⟩ := hF3
  obtain ⟨g, hg⟩ := isConj_iff.mp hyD
  subst hg
  obtain ⟨b, hbD, hbQ, hbcode, hbQa⟩ := exists_mem_Qa_of_class hF h33 h34a h34b S hw hU
    h1235.1 (fun r hr => h1235.2.2.2 r hr) hyM hyQ hk hAy hi hEi
  have hcomm_b : ∀ {c : G} (hc : IsConj S.z c) (hcM : c ∈ S.M) (hcQ : c ∉ S.QG) {kc : Nat},
      SMG.Acts S φ c (applyCols (tvCols kc)) → applyCols (tvCols kc) (wt i) = wt i →
      Commute b c := fun {c} hc hcM hcQ kc hAc hfc => by
    have hcl : S.cl (c * b * c⁻¹) = S.cl b := by
      apply φ.injective
      apply SMG.code_injective
      rw [hAc b hbQ, hbcode, hfc]
    have hfix := (S.cl_mem_fixQt_iff hcM hbQ).mpr hcl
    exact (S.commute_of_cl_mem_fixQt hcM (fixQt_eq_of_smithL6E34a h34a S hw hU hc hcM hcQ)
      hbQ hfix).symm
  have hbt := hcomm_b ht htM htQ hAt hfixt
  have hbu := hcomm_b hu huM huQ hAu hfixu
  have hbK : b ∈ K := hQK (mem_inf.mpr ⟨hbQ, mem_cent2.mpr ⟨hbt, hbu⟩⟩)
  obtain ⟨hb, rfl⟩ := isConj_iff.mp hbD
  have hyQb : hb⁻¹ * (g * S.z * g⁻¹) * hb ∈ S.QG := by
    have hQ : g⁻¹ * (hb * S.z * hb⁻¹) * g ∈ S.QG := (SME.mem_Qa_iff S g _).mp hbQa
    refine SME.mem_Qa_symm S hQ fun e => hyQ ?_
    rw [← e]
    exact hbQ
  have hyb : g * S.z * g⁻¹ ≠ hb * S.z * hb⁻¹ := fun e => hyQ (e ▸ hbQ)
  obtain ⟨q, hqt, hqu, hq⟩ := exists_conj_eq_mul_of_mem_Qa hE S hw hU ht hu htu hbt hbu hyD hyQb
    hyb hyt hyu
  have hqH : q ∈ cent2 t u := mem_cent2.mpr ⟨hqt, hqu⟩
  have hby : hb * S.z * hb⁻¹ * (g * S.z * g⁻¹) ∈ K := hq ▸ hnK q hqH _ hbK
  have := K.mul_mem (K.inv_mem hbK) hby
  rwa [inv_mul_cancel_left] at this

theorem card_mul_card_closure_le (S : Setting G) (ψ : Mbar0 S ≃* ↥T6) {C : Subgroup G}
    (hCM : C ≤ S.M) (kt ku : Fin 1953)
    (hI : ∀ k : Fin 1953, Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) →
      ∃ y ∈ C, ∃ (hyM : y ∈ S.M)
        (h0 : (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
        ψ ⟨⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩) :
    Nat.card ↥(S.QG ⊓ C) * Nat.card (closure (tvP '' {k : Fin 1953 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) ≤ Nat.card C := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  let r : C →* S.Mbar := SMH.toMbar S hCM
  have hrker : ∀ c : C, c ∈ r.ker ↔ (c : G) ∈ S.QG := fun c => by
    rw [MonoidHom.mem_ker]
    exact ⟨fun h => (S.ρ_eq_one_iff ⟨c, hCM c.2⟩).mp (congrArg Subtype.val h),
      fun h => Subtype.ext ((S.ρ_eq_one_iff ⟨c, hCM c.2⟩).mpr h)⟩
  have hker : Nat.card ↥(S.QG ⊓ C) ≤ Nat.card r.ker := by
    refine Nat.card_le_card_of_injective
      (fun q => ⟨⟨q.1, (mem_inf.mp q.2).2⟩, (hrker _).mpr (mem_inf.mp q.2).1⟩) fun a b hab => ?_
    exact Subtype.ext (congrArg (fun w : r.ker => ((w : C) : G)) hab)
  have hle : closure (tvP '' {k : Fin 1953 | Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})
      ≤ ((r.range.subgroupOf (Mbar0 S)).map ψ.toMonoidHom).map T6.subtype := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨k, ⟨hk1, hk2⟩, rfl⟩
    obtain ⟨y, hyC, hyM, h0, hψ⟩ := hI k hk1 hk2
    refine ⟨_, ⟨⟨_, h0⟩, ?_, rfl⟩, congrArg Subtype.val hψ⟩
    show _ ∈ r.range.subgroupOf (Mbar0 S)
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨y, hyC⟩, Subtype.ext rfl⟩
  have hrange : Nat.card (closure (tvP '' {k : Fin 1953 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) ≤ Nat.card r.range := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective ψ.injective]
    exact Nat.card_le_card_of_injective (fun w => ⟨(w.1 : S.Mbar), w.2⟩) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun w : r.range => (w : S.Mbar)) hab))
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv] at h
  rw [h, mul_comm]
  exact Nat.mul_le_mul hrange hker

set_option maxHeartbeats 400000 in
theorem smithL6E261_of (h34a : SmithL6E34a) (h34b : SmithL6E34b) (hLoc : SmithL62LocalInput)
    (hE : SmithL6E23a) (hC : SmithL6Compat) (h33 : SmithL6E33) (hF : E23FourFacts)
    (hwt : ∀ i < 1395, wt i ≠ 0)
    (hF3 : ∀ kt ku k : Fin 1953, orderOf (tvP kt * tvP ku) = 3 → Commute (tvP k) (tvP kt) →
      Commute (tvP k) (tvP ku) → ∃ i < 1395, InE k i ∧
        applyCols (tvCols kt) (wt i) = wt i ∧ applyCols (tvCols ku) (wt i) = wt i)
    (hM4 : ∀ kt ku : Fin 1953, orderOf (tvP kt * tvP ku) = 3 →
      20160 ≤ Nat.card (closure (tvP '' {k : Fin 1953 |
        Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)}))) :
    SmithL6E261 := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ htu
  classical
  obtain ⟨K, hKH, hzK, hKs, hQK, hconjK, hnK⟩ :=
    exists_simple_le_cent2 hE S hw hU ht hu htM huM htQ huQ htu
  refine ⟨K, hzK, fun n hn => mem_cent2.mp (hKH hn), ?_⟩
  obtain ⟨φ, ψ, h1235, h4, hcomp, h2', h3'⟩ := hC G S hw hU
  obtain ⟨hext, hcard9, -, -, -⟩ := hE G S hw hU t u ht hu htM huM htQ huQ htu
  have hti : t⁻¹ = t := SME.inv_eq_of_isConj S ht
  have hui : u⁻¹ = u := SME.inv_eq_of_isConj S hu
  obtain ⟨kt, h0t, hkt⟩ := h2' t htM ht htQ
  obtain ⟨ku, h0u, hku⟩ := h2' u huM hu huQ
  have hρ1 : ∀ {c : G} (hc : c ∈ S.M), S.ρ ⟨c, hc⟩ = 1 ↔ c ∈ S.QG := fun {c} hc =>
    S.ρ_eq_one_iff ⟨c, hc⟩
  have hψeq : ∀ {c d : G} (hc : c ∈ S.M) (hd : d ∈ S.M)
      (h0c : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S)
      (h0d : (⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
      ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0c⟩ = ψ ⟨⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩, h0d⟩ →
        S.ρ ⟨c, hc⟩ = S.ρ ⟨d, hd⟩ := fun {c d} hc hd h0c h0d h => by
    have := ψ.injective h
    exact congrArg (fun w : Mbar0 S => ((w : S.Mbar) : S.O)) this
  have hcommQ : ∀ {c d : G} (hc : c ∈ S.M) (hd : d ∈ S.M)
      (h0c : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S)
      (h0d : (⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S) {kc kd : Fin 1953},
      ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0c⟩ = ⟨tvP kc, tvP_mem kc⟩ →
      ψ ⟨⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩, h0d⟩ = ⟨tvP kd, tvP_mem kd⟩ →
      Commute (tvP kc) (tvP kd) → (c * d)⁻¹ * (d * c) ∈ S.QG := by
    intro c d hc hd h0c h0d kc kd hψc hψd hcd
    have h1 : ψ (⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0c⟩ * ⟨⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩, h0d⟩) =
        ψ (⟨⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩, h0d⟩ * ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0c⟩) := by
      refine (map_mul ψ _ _).trans ((congrArg₂ (· * ·) hψc hψd).trans ?_)
      refine Eq.trans ?_ ((congrArg₂ (· * ·) hψd hψc).symm.trans (map_mul ψ _ _).symm)
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hcd.eq
    have h2 : S.ρ ⟨c, hc⟩ * S.ρ ⟨d, hd⟩ = S.ρ ⟨d, hd⟩ * S.ρ ⟨c, hc⟩ :=
      congrArg (fun w : Mbar0 S => ((w : S.Mbar) : S.O)) (ψ.injective h1)
    rw [← map_mul, ← map_mul] at h2
    exact inv_mul_mem_QG_of_ρ_eq S h2
  have hord : orderOf (tvP kt * tvP ku) = 3 := by
    let τ : Mbar0 S := ⟨⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩, h0t⟩
    let υ : Mbar0 S := ⟨⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩, h0u⟩
    have hψτυ : ψ (τ * υ) = ⟨tvP kt * tvP ku, T6.mul_mem (tvP_mem kt) (tvP_mem ku)⟩ :=
      (map_mul ψ τ υ).trans ((congrArg₂ (· * ·) hkt hku).trans (Subtype.ext rfl))
    have e1 : orderOf (tvP kt * tvP ku) = orderOf (τ * υ) := by
      rw [← MulEquiv.orderOf_eq ψ, hψτυ, Subgroup.orderOf_mk]
    have e2 : (((τ * υ : Mbar0 S) : S.Mbar) : S.O) = S.ρ (⟨t, htM⟩ * ⟨u, huM⟩) := by
      rw [map_mul]; rfl
    rw [e1, ← Subgroup.orderOf_coe (τ * υ), ← Subgroup.orderOf_coe ((τ * υ : Mbar0 S) : S.Mbar),
      e2]
    have hdvd : orderOf (S.ρ (⟨t, htM⟩ * ⟨u, huM⟩)) ∣ 3 := by
      refine (orderOf_map_dvd S.ρ _).trans ?_
      rw [← Subgroup.orderOf_coe]
      exact htu.symm ▸ dvd_refl _
    have hne1 : S.ρ (⟨t, htM⟩ * ⟨u, huM⟩) ≠ 1 := fun h =>
      not_mem_QG_of_orderOf_three S htu ((S.ρ_eq_one_iff _).mp h)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · exact h
  have hlift : ∀ k : Fin 1953, Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) →
      ∃ y ∈ K, ∃ (hyM : y ∈ S.M)
        (h0 : (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
        ψ ⟨⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩ := by
    intro k hkt' hku'
    obtain ⟨x, hxM, hx, hxQ, h0x, hψx⟩ := h3' k
    have hxi : x⁻¹ = x := SME.inv_eq_of_isConj S hx
    have hxt := hcommQ hxM htM h0x h0t hψx hkt hkt'
    have hxu := hcommQ hxM huM h0x h0u hψx hku hku'
    have hty : t * x * t⁻¹ * x⁻¹ ∈ S.QG := by
      have e1 : (x * t)⁻¹ * (t * x) = t * x * t * x := by rw [mul_inv_rev, hti, hxi]; group
      rw [hti, hxi]
      rwa [e1] at hxt
    have huy : u * x * u⁻¹ * x⁻¹ ∈ S.QG := by
      have e1 : (x * u)⁻¹ * (u * x) = u * x * u * x := by rw [mul_inv_rev, hui, hxi]; group
      rw [hui, hxi]
      rwa [e1] at hxu
    obtain ⟨y, hyD, hxy, hyt, hyu⟩ := exists_lift_commute h34a h34b hLoc S hw hU ht hu htM huM
      htQ htu hx hxM hxQ hty huy
    have hyM : y ∈ S.M := by
      have := S.M.mul_mem hxM (S.QG_le_M hxy)
      rwa [mul_inv_cancel_left] at this
    have hyQ : y ∉ S.QG := fun hyQ => hxQ (by
      have := S.QG.mul_mem hyQ (S.QG.inv_mem hxy)
      rwa [show y * (x⁻¹ * y)⁻¹ = x by group] at this)
    have hρy : S.ρ ⟨y, hyM⟩ = S.ρ ⟨x, hxM⟩ :=
      (ρ_eq_of_inv_mul_mem_QG S (a := ⟨x, hxM⟩) (b := ⟨y, hyM⟩) hxy).symm
    have h0y : (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S := by
      have : (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) = ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ :=
        Subtype.ext hρy
      exact (congrArg (fun w : S.Mbar => w ∈ Mbar0 S) this).mpr h0x
    have hψy : ψ ⟨⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩, h0y⟩ = ⟨tvP k, tvP_mem k⟩ := by
      have : (⟨⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩, h0y⟩ : Mbar0 S) =
          ⟨⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩, h0x⟩ := Subtype.ext (Subtype.ext hρy)
      exact (congrArg ψ this).trans hψx
    exact ⟨y, mem_of_acts h34a h34b hE h33 hF hwt S hw hU ht hu htM huM htQ huQ htu h1235 hQK
      hnK hyD hyM hyQ hyt hyu k.2 (acts_of_compat (k := k) hcomp hyM h0y hψy)
      (acts_of_compat (k := kt) hcomp htM h0t hkt) (acts_of_compat (k := ku) hcomp huM h0u hku)
      (hF3 kt ku k hord hkt' hku'), hyM, h0y, hψy⟩
  have hCM : K ⊓ centralizer ({S.z} : Set G) ≤ S.M := inf_le_right
  have hcardC : 10321920 ≤ Nat.card ↥(K ⊓ centralizer ({S.z} : Set G)) := by
    have hb := card_mul_card_closure_le S ψ hCM kt ku fun k hk1 hk2 => by
        obtain ⟨y, hyK, hyM, h0y, hψy⟩ := hlift k hk1 hk2
        exact ⟨y, mem_inf.mpr ⟨hyK, hyM⟩, hyM, h0y, hψy⟩
    have hQ : 2 ^ 9 ≤ Nat.card ↥(S.QG ⊓ (K ⊓ centralizer ({S.z} : Set G))) := by
      rw [← hcard9]
      refine Subgroup.card_le_of_le fun q hq => ?_
      exact mem_inf.mpr ⟨(mem_inf.mp hq).1, mem_inf.mpr ⟨hQK hq, S.QG_le_M (mem_inf.mp hq).1⟩⟩
    calc 10321920 = 2 ^ 9 * 20160 := by norm_num
      _ ≤ Nat.card ↥(S.QG ⊓ (K ⊓ centralizer ({S.z} : Set G))) *
          Nat.card (closure (tvP '' {k : Fin 1953 |
            Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) :=
          Nat.mul_le_mul hQ (hM4 kt ku hord)
      _ ≤ _ := hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ht
  obtain ⟨f, hf⟩ : ∃ f : G →* G, f = (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by rw [hf]; exact (MulAut.conj g⁻¹).injective
  have hfapp : ∀ a : G, f a = g⁻¹ * a * g := fun a => by
    simp [hf, MulAut.conj_apply]
  have hK'M : K.map f ≤ S.M := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hfapp, mem_centralizer_singleton_iff]
    have hkt := (mem_cent2.mp (hKH hk)).1
    rw [← hg] at hkt
    simp only [Commute, SemiconjBy] at hkt
    calc g⁻¹ * k * g * S.z = g⁻¹ * (k * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * k) * g := by rw [hkt]
      _ = S.z * (g⁻¹ * k * g) := by group
  haveI : IsSimpleGroup (K.map f) := (Subgroup.equivMapOfInjective K f hfinj).symm.isSimpleGroup
  have hxK : g⁻¹ * S.z * g ∈ K.map f := ⟨S.z, hzK, hfapp _⟩
  have hx : IsConj S.z (g⁻¹ * S.z * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hxQ : g⁻¹ * S.z * g ∉ S.QG := fun h => htQ (by
    have := SME.mem_Qa_symm S (g := g) (k := 1) (by simpa using h) (by
      rw [hg]
      simpa using fun e : S.z = t => htQ (e ▸ S.z_mem_QG))
    simpa [hg] using this)
  have hcard' : 10321920 ≤ Nat.card ↥(K.map f ⊓ centralizer ({g⁻¹ * S.z * g} : Set G)) := by
    refine hcardC.trans (Nat.card_le_card_of_injective
      (fun c => ⟨f c, mem_inf.mpr ⟨⟨c, (mem_inf.mp c.2).1, rfl⟩, ?_⟩⟩) fun a b hab => ?_)
    · rw [hfapp, mem_centralizer_singleton_iff]
      have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
      calc g⁻¹ * (c : G) * g * (g⁻¹ * S.z * g) = g⁻¹ * ((c : G) * S.z) * g := by group
        _ = g⁻¹ * (S.z * c) * g := by rw [hc]
        _ = g⁻¹ * S.z * g * (g⁻¹ * c * g) := by group
    · exact Subtype.ext (hfinj (congrArg Subtype.val hab))
  have h2K : 2 < Nat.card (K.map f) :=
    lt_of_lt_of_le (by norm_num) (hcard'.trans (Subgroup.card_le_of_le inf_le_left))
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_of_card_centralizer hC S hw hU hK'M h2K hxK hx hxQ hcard'
  exact ⟨(Subgroup.equivMapOfInjective K f hfinj).trans e⟩

end E261

end CFSG.GF2Type.SmithTypeE.L6Ident
