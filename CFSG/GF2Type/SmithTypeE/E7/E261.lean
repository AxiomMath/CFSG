module

public import CFSG.GF2Type.SmithTypeE.E7.Ident
public import CFSG.GF2Type.SmithTypeE.E7.Pair
public import CFSG.GF2Type.SmithTypeE.E7.E23a
public import CFSG.GF2Type.SmithTypeE.E7.IdentSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithD6 (wt tvCols applyCols)
open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.GF2Type.SmithTypeE.L6Ident (conj_inv_mem_M_of_commute)

section Codes

theorem code32_tvEquiv {k : ℕ} (hk : k < 365211) (v : V) :
    code32 (tvEquiv k v) = applyCols (tvCols k) (code32 v) := by
  have h := tvEquiv_decode hk (code32 v)
  rw [decode32_code32] at h
  rw [h, code32_decode32 (applyCols_lt (size_tvCols k) (fun _ hc => tvCols_lt k hc) _)]

end Codes

section E261

variable {G : Type} [Group G] [Finite G]

theorem acts_of_compat {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] V} {ψ : S.Mbar ≃* ↥TD6}
    (hcomp : ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)))
    {c : G} (hc : c ∈ S.M) {k : Fin 365211}
    (hψ : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) :
    Acts S φ c (applyCols (tvCols k.val)) := by
  intro u hu
  rw [hcomp c hc u hu, hψ, rhoMod_tvP, code32_tvEquiv k.2]

theorem exists_conj_eq_mul_of_mem_Qa (hE : SmithE7E23a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {t u h a : G}
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
    (commute_conj_inv_E7 h hat) (commute_conj_inv_E7 h hau)
  refine ⟨h * q * h⁻¹, ?_, ?_, ?_⟩
  · have := commute_conj_inv_E7 h⁻¹ hqt
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * t * h) * h⁻¹ = t by group] at this
  · have := commute_conj_inv_E7 h⁻¹ hqu
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * u * h) * h⁻¹ = u by group] at this
  · calc h * q * h⁻¹ * (h * S.z * h⁻¹) * (h * q * h⁻¹)⁻¹ = h * (q * S.z * q⁻¹) * h⁻¹ := by group
      _ = h * (S.z * (h⁻¹ * a * h)) * h⁻¹ := by rw [hq]
      _ = h * S.z * h⁻¹ * a := by group

theorem mem_of_acts (hF : E23FourFacts7) (h33 : SmithE7E33) (h34a : SmithE7E34a)
    (h34b : SmithE7E34b) (hE : SmithE7E23a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    {φ : S.Qt ≃ₗ[ZMod 2] V} (h1235 : SmithE7Clauses1235 S φ)
    {K : Subgroup G} (hQK : S.QG ⊓ cent2 t u ≤ K)
    (hnK : ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {y : G} (hyD : IsConj S.z y) (hyM : y ∈ S.M) (hyQ : y ∉ S.QG) (hyt : Commute y t)
    (hyu : Commute y u) {k kt ku : Nat} (hk : k < 365211)
    (hAy : Acts S φ y (applyCols (tvCols k))) (hAt : Acts S φ t (applyCols (tvCols kt)))
    (hAu : Acts S φ u (applyCols (tvCols ku)))
    (hF3 : ∃ i < 75735, InE k i ∧ applyCols (tvCols kt) (wt i) = wt i ∧
      applyCols (tvCols ku) (wt i) = wt i) : y ∈ K := by
  obtain ⟨i, hi, hEi, hfixt, hfixu⟩ := hF3
  obtain ⟨g, hg⟩ := isConj_iff.mp hyD
  subst hg
  obtain ⟨b, hbD, hbQ, hbcode, hbQa⟩ := exists_mem_Qa_of_class hF h33 h34a h34b S hw hU
    h1235.1 (fun r hr => h1235.2.2.2 r hr) hyM hyQ hk hAy hi hEi
  have hcomm_b : ∀ {c : G} (hc : IsConj S.z c) (hcM : c ∈ S.M) (hcQ : c ∉ S.QG) {kc : Nat},
      Acts S φ c (applyCols (tvCols kc)) → applyCols (tvCols kc) (wt i) = wt i →
      Commute b c := fun {c} hc hcM hcQ kc hAc hfc => by
    have hcl : S.cl (c * b * c⁻¹) = S.cl b := by
      apply psi_inj S φ
      rw [hAc b hbQ, hbcode, hfc]
    have hfix := (S.cl_mem_fixQt_iff hcM hbQ).mpr hcl
    exact (S.commute_of_cl_mem_fixQt hcM (fixQt_eq_of_smithE7E34a h34a S hw hU hc hcM hcQ)
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

theorem card_mul_card_closure_le (S : Setting G) (ψ : S.Mbar ≃* ↥TD6) {C : Subgroup G}
    (hCM : C ≤ S.M) (kt ku : Fin 365211)
    (hI : ∀ k : Fin 365211, Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) →
      ∃ y ∈ C, ∃ hyM : y ∈ S.M,
        ψ ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) :
    Nat.card ↥(S.QG ⊓ C) * Nat.card (closure (tvP '' {k : Fin 365211 |
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
  have hle : closure (tvP '' {k : Fin 365211 | Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})
      ≤ (r.range.map ψ.toMonoidHom).map TD6.subtype := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨k, ⟨hk1, hk2⟩, rfl⟩
    obtain ⟨y, hyC, hyM, hψ⟩ := hI k hk1 hk2
    refine ⟨_, ⟨_, ⟨⟨y, hyC⟩, Subtype.ext rfl⟩, rfl⟩, congrArg Subtype.val hψ⟩
  have hrange : Nat.card (closure (tvP '' {k : Fin 365211 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) ≤ Nat.card r.range := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective ψ.injective]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv] at h
  rw [h, mul_comm]
  exact Nat.mul_le_mul hrange hker

end E261

section Main

set_option maxHeartbeats 400000 in
theorem smithE7E261_of (h34a : SmithE7E34a) (h34b : SmithE7E34b) (hLoc : SmithE7LocalInput)
    (hE : SmithE7E23a) (hC : SmithE7Compat) (h33 : SmithE7E33) (hF : E23FourFacts7) :
    SmithE7E261 := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ htu
  classical
  obtain ⟨K, hKH, hzK, hKs, hQK, hconjK, hnK⟩ :=
    exists_simple_le_cent2 hE S hw hU ht hu htM huM htQ huQ htu
  refine ⟨K, hzK, fun n hn => mem_cent2.mp (hKH hn), ?_⟩
  obtain ⟨φ, ψ, h1235, h4, hcomp, h2', h3'⟩ := hC G S hw hU
  obtain ⟨hext, hcard17, -, -, -⟩ := hE G S hw hU t u ht hu htM huM htQ huQ htu
  obtain ⟨kt, hkt⟩ := h2' t htM ht htQ
  obtain ⟨ku, hku⟩ := h2' u huM hu huQ
  have hord : orderOf (tvP kt * tvP ku) = 3 := orderOf_tvP_of_compat ψ htM huM hkt hku htu
  have hlift : ∀ k : Fin 365211, Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) →
      ∃ y ∈ K, ∃ hyM : y ∈ S.M,
        ψ ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ := by
    intro k hkt' hku'
    obtain ⟨y, hyM, hyD, hyQ, hyt, hyu, hψy⟩ :=
      exists_lift_tv h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hkt hku k hkt' hku'
    exact ⟨y, mem_of_acts hF h33 h34a h34b hE S hw hU ht hu htM huM htQ huQ htu h1235 hQK
      hnK hyD hyM hyQ hyt hyu k.2 (acts_of_compat hcomp hyM hψy)
      (acts_of_compat hcomp htM hkt) (acts_of_compat hcomp huM hku)
      (hF3_holds kt ku k hord hkt' hku'), hyM, hψy⟩
  have hCM : K ⊓ centralizer ({S.z} : Set G) ≤ S.M := inf_le_right
  have hcardC : 136982613196800 ≤ Nat.card ↥(K ⊓ centralizer ({S.z} : Set G)) := by
    have hb := card_mul_card_closure_le S ψ hCM kt ku fun k hk1 hk2 => by
        obtain ⟨y, hyK, hyM, hψy⟩ := hlift k hk1 hk2
        exact ⟨y, mem_inf.mpr ⟨hyK, hyM⟩, hyM, hψy⟩
    have hQ : 2 ^ 17 ≤ Nat.card ↥(S.QG ⊓ (K ⊓ centralizer ({S.z} : Set G))) := by
      rw [← hcard17]
      refine Subgroup.card_le_of_le fun q hq => ?_
      exact mem_inf.mpr ⟨(mem_inf.mp hq).1, mem_inf.mpr ⟨hQK hq, S.QG_le_M (mem_inf.mp hq).1⟩⟩
    calc 136982613196800 = 2 ^ 17 * 1045094400 := by norm_num
      _ ≤ Nat.card ↥(S.QG ⊓ (K ⊓ centralizer ({S.z} : Set G))) *
          Nat.card (closure (tvP '' {k : Fin 365211 |
            Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) :=
          Nat.mul_le_mul hQ (hM4_holds kt ku hord)
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
  have hcard' : 136982613196800 ≤ Nat.card ↥(K.map f ⊓ centralizer ({g⁻¹ * S.z * g} : Set G)) := by
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
  obtain ⟨e⟩ := nonempty_mulEquiv_omega_of_card_centralizer hC S hw hU hK'M h2K hxK hx hxQ hcard'
  exact ⟨(Subgroup.equivMapOfInjective K f hfinj).trans e⟩

end Main

end CFSG.GF2Type.SmithTypeE.E7
