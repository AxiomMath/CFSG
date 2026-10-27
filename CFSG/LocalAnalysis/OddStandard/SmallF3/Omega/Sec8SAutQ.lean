module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SOddE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SConjO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Au
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec8sau_conj_mem_centralizer {E : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (E : Set G)) (hc : c ∈ centralizer (E : Set G)) :
    n * c * n⁻¹ ∈ centralizer (E : Set G) :=
  (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer (E : Set G))).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G)) c n hc hn

private theorem sec8sau_conj_mem {t : G} {B E : Subgroup G}
    (hcent : E ⊓ centralizer ({t} : Set G) = B) {x : G}
    (hxX : x ∈ normalizer (E : Set G)) (hxt : x ∈ centralizer ({t} : Set G))
    {b : G} (hb : b ∈ B) : x * b * x⁻¹ ∈ B := by
  have hb' : b ∈ E ⊓ centralizer ({t} : Set G) := by rw [hcent]; exact hb
  have hbE : b ∈ E := hb'.1
  have hbCt : b ∈ centralizer ({t} : Set G) := hb'.2
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
  have hxt_conj : x * t * x⁻¹ = t := by rw [hxt']; group
  have hxinv_t : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (x * t * x⁻¹) := by rw [hxt_conj]
      _ = t * x⁻¹ := by group
  have hcomm : (x * b * x⁻¹) * t = t * (x * b * x⁻¹) := by
    have hbtc : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hbCt
    calc (x * b * x⁻¹) * t = x * b * (x⁻¹ * t) := by group
      _ = x * b * (t * x⁻¹) := by rw [hxinv_t]
      _ = x * (b * t) * x⁻¹ := by group
      _ = x * (t * b) * x⁻¹ := by rw [hbtc]
      _ = (x * t) * b * x⁻¹ := by group
      _ = (t * x) * b * x⁻¹ := by rw [hxt']
      _ = t * (x * b * x⁻¹) := by group
  rw [← hcent]
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxX b).mp hbE,
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩

private theorem sec8sau_mem_normalizer_inf {t : G} {B E : Subgroup G}
    (hcent : E ⊓ centralizer ({t} : Set G) = B) :
    normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (B : Set G) := by
  intro x hx
  obtain ⟨hxX, hxt⟩ := Subgroup.mem_inf.mp hx
  have hxX' : x⁻¹ ∈ normalizer (E : Set G) := (normalizer (E : Set G)).inv_mem hxX
  have hxt' : x⁻¹ ∈ centralizer ({t} : Set G) := (centralizer ({t} : Set G)).inv_mem hxt
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact fun hb => sec8sau_conj_mem hcent hxX hxt hb
  · intro hb
    have h := sec8sau_conj_mem hcent hxX' hxt' hb
    have h' : x⁻¹ * (x * b * x⁻¹) * x = b := by group
    simpa only [inv_inv, h'] using h

open scoped Pointwise in
private theorem sec8sau_mem_sup_mul {t : G} {E : Subgroup G} {y : G}
    (hy : y ∈ (normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) ⊔
      centralizer (E : Set G)) :
    ∃ x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G),
      ∃ c ∈ centralizer (E : Set G), y = x * c := by
  have hle : normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (centralizer (E : Set G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => sec8sau_conj_mem_centralizer hx.1 hc, fun hc => ?_⟩
    have h := sec8sau_conj_mem_centralizer ((normalizer (E : Set G)).inv_mem hx.1) hc
    have h' : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
    rwa [h'] at h
  have hmem : y ∈ ((normalizer (E : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :
      Set G) * ((centralizer (E : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hy
  obtain ⟨x, hx, c, hc, rfl⟩ := hmem
  exact ⟨x, hx, c, hc, rfl⟩

theorem sec8s_autQ [Finite G] (h8A : Asc82Lemma8A) {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) :
    QuotEquivTo (normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ⊔ centralizer (E : Set G))
      (zpowers t ⊔ centralizer (E : Set G)) ↥(autIn (centralizer ({t} : Set G)) B) := by
  classical
  let X : Subgroup G := normalizer (E : Set G)
  let Ct : Subgroup G := centralizer ({t} : Set G)
  let CE : Subgroup G := centralizer (E : Set G)
  let H : Subgroup G := X ⊓ Ct ⊔ CE
  let K : Subgroup G := zpowers t ⊔ CE
  let NB : Subgroup G := normalizer (B : Set G)
  let A : Subgroup G := Asub8 t B
  let O : Subgroup G := oddCoreIn (Nsub8 t B)
  change QuotEquivTo H K ↥(autIn Ct B)
  have ht2 : t * t = 1 := by rw [← pow_two, ← hE.ctx.involution, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hBE : B ≤ E := by rw [← hE.cent_t]; exact inf_le_left
  have hBCt : B ≤ Ct := by rw [← hE.cent_t]; exact inf_le_right
  have hEC : E ≤ CE := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact CFSG.Open.IsElemAbelian.comm hE.elem.1 hx he
  have hBC : B ≤ CE := hBE.trans hEC
  have htX : t ∈ X := by
    show t ∈ normalizer (E : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact hE.t_norm e
    · intro he
      have h2 := hE.t_norm (t * e * t⁻¹) he
      have h3 : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
          _ = e := by rw [ht2]; group
      rwa [h3] at h2
  have hAX : A ≤ X := by
    change zpowers t ⊔ B ≤ normalizer (E : Set G)
    exact sup_le (zpowers_le.mpr htX) (hBE.trans (Subgroup.le_normalizer))
  have hAK : A ≤ K := by
    change zpowers t ⊔ B ≤ zpowers t ⊔ CE
    exact sup_le le_sup_left (hBC.trans le_sup_right)
  have h8A1 := h8A G t L S z g B hE.ctx
  have hcentA : centralizer (A : Set G) = A ⊔ O := (h8A1.1.trans h8A1.2).symm
  have hOleCentA : O ≤ centralizer (A : Set G) := by rw [hcentA]; exact le_sup_right
  let P : Subgroup G := ((autIn Ct B).comap (B.normalizerMonoidHom)).map NB.subtype
  have hHcP : X ⊓ Ct ≤ P := by
    intro x hx
    obtain ⟨hxX, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxNB : x ∈ NB := sec8sau_mem_normalizer_inf hE.cent_t hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxNB⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact sec1011_conjAut_mem hxt hxNB
  have hCEP : CE ≤ P := by
    intro c hc
    have hcNB : c ∈ NB :=
      (Subgroup.centralizer_le hBE).trans (Subgroup.centralizer_le_normalizer (B : Set G)) hc
    refine Subgroup.mem_map.mpr ⟨⟨c, hcNB⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hconj : B.normalizerMonoidHom ⟨c, hcNB⟩ = 1 := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      calc (((B.normalizerMonoidHom ⟨c, hcNB⟩) b : ↥B) : G)
          = ((⟨c, hcNB⟩ : ↥NB) : G) * (b : G) * ((⟨c, hcNB⟩ : ↥NB) : G)⁻¹ :=
            Subgroup.normalizerMonoidHom_apply_apply_coe B ⟨c, hcNB⟩ b
        _ = c * (b : G) * c⁻¹ := rfl
        _ = (b : G) := by
            have hcb : (b : G) * c = c * (b : G) :=
              Subgroup.mem_centralizer_iff.mp hc b (hBE b.2)
            rw [← hcb]; group
    rw [hconj]
    exact (autIn Ct B).one_mem
  have hHP : H ≤ P := by
    change X ⊓ Ct ⊔ CE ≤ P
    exact sup_le hHcP hCEP
  have hHNB : H ≤ NB := by
    intro h hh
    have hhP : h ∈ P := hHP hh
    obtain ⟨y, _, hyg⟩ := Subgroup.mem_map.mp hhP
    rw [← hyg]
    exact y.2
  let φ₀ : ↥H →* MulAut ↥B := (B.normalizerMonoidHom).comp (Subgroup.inclusion hHNB)
  have hrange : ∀ h : ↥H, φ₀ h ∈ autIn Ct B := by
    intro h
    change B.normalizerMonoidHom (Subgroup.inclusion hHNB h) ∈ autIn Ct B
    have hhP : (h : G) ∈ P := hHP h.2
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hhP
    have hy' : B.normalizerMonoidHom y ∈ autIn Ct B := Subgroup.mem_comap.mp hy
    have hyy : y = ⟨(h : G), hHNB h.2⟩ := Subtype.ext hyg
    rw [hyy] at hy'
    exact hy'
  let φ : ↥H →* ↥(autIn Ct B) := φ₀.codRestrict (autIn Ct B) hrange
  have hphi_apply : ∀ (h : ↥H) (b : ↥B),
      (((φ h : MulAut ↥B) b : ↥B) : G) = (h : G) * (b : G) * (h : G)⁻¹ := by
    intro h b
    have h1 : (φ h : MulAut ↥B) = φ₀ h := rfl
    rw [h1]
    change ((B.normalizerMonoidHom (Subgroup.inclusion hHNB h) b : ↥B) : G) =
      (h : G) * (b : G) * (h : G)⁻¹
    calc (((B.normalizerMonoidHom (Subgroup.inclusion hHNB h)) b : ↥B) : G)
        = ((Subgroup.inclusion hHNB h : ↥NB) : G) * (b : G) *
            ((Subgroup.inclusion hHNB h : ↥NB) : G)⁻¹ :=
          Subgroup.normalizerMonoidHom_apply_apply_coe B (Subgroup.inclusion hHNB h) b
      _ = (h : G) * (b : G) * (h : G)⁻¹ := by rw [Subgroup.coe_inclusion]
  have hsurj : Function.Surjective φ := by
    intro α
    obtain ⟨y, hyCt, hyN, hαeq⟩ :=
      sec1011_exists_conjAut (H := Ct) (Y := B) (α := (α : MulAut ↥B)) α.2
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyCt
    obtain ⟨o, hoO, hoXy⟩ := sec8s_conj_oddCore hE hyt hyN
    let x : G := o⁻¹ * y
    have htA : t ∈ A := by
      change t ∈ zpowers t ⊔ B
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have ho_t : o * t = t * o :=
      (Subgroup.mem_centralizer_iff.mp (hOleCentA hoO) t htA).symm
    have ho_t_inv : o⁻¹ * t = t * o⁻¹ := by
      have hconj : o * t * o⁻¹ = t := by rw [ho_t]; group
      calc o⁻¹ * t = o⁻¹ * (o * t * o⁻¹) := by rw [hconj]
        _ = t * o⁻¹ := by group
    have hx_t : x * t = t * x := by
      change (o⁻¹ * y) * t = t * (o⁻¹ * y)
      calc (o⁻¹ * y) * t = o⁻¹ * (y * t) := by group
        _ = o⁻¹ * (t * y) := by rw [hyt]
        _ = (o⁻¹ * t) * y := by group
        _ = (t * o⁻¹) * y := by rw [ho_t_inv]
        _ = t * (o⁻¹ * y) := by group
    have hxX : x ∈ X := hoXy
    have hxCt : x ∈ Ct := Subgroup.mem_centralizer_singleton_iff.mpr hx_t
    have hxH : x ∈ H := by
      change x ∈ X ⊓ Ct ⊔ CE
      exact Subgroup.mem_sup_left ⟨hxX, hxCt⟩
    refine ⟨⟨x, hxH⟩, ?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hphi_apply, hαeq, sec1011_conjAut_apply]
    change (o⁻¹ * y) * (b : G) * (o⁻¹ * y)⁻¹ = y * (b : G) * y⁻¹
    have hybB : y * (b : G) * y⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hyN b).mp b.2
    have hybA : y * (b : G) * y⁻¹ ∈ A := by
      change y * (b : G) * y⁻¹ ∈ zpowers t ⊔ B
      exact Subgroup.mem_sup_right hybB
    have ho_comm : o * (y * (b : G) * y⁻¹) = (y * (b : G) * y⁻¹) * o :=
      (Subgroup.mem_centralizer_iff.mp (hOleCentA hoO) (y * (b : G) * y⁻¹) hybA).symm
    calc (o⁻¹ * y) * (b : G) * (o⁻¹ * y)⁻¹ = o⁻¹ * (y * (b : G) * y⁻¹) * o := by group
      _ = o⁻¹ * ((y * (b : G) * y⁻¹) * o) := by group
      _ = o⁻¹ * (o * (y * (b : G) * y⁻¹)) := by rw [ho_comm]
      _ = y * (b : G) * y⁻¹ := by group
  have hker_le : φ.ker ≤ K.subgroupOf H := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    rw [Subgroup.mem_subgroupOf]
    have hcommB : ∀ b : ↥B, (h : G) * (b : G) = (b : G) * (h : G) := by
      intro b
      have h1 : (φ h : MulAut ↥B) b = b := by rw [hh]; rfl
      have h2 := hphi_apply h b
      rw [h1] at h2
      have h2' : (h : G) * (b : G) * (h : G)⁻¹ = (b : G) := h2.symm
      calc (h : G) * (b : G) = ((h : G) * (b : G) * (h : G)⁻¹) * (h : G) := by group
        _ = (b : G) * (h : G) := by rw [h2']
    obtain ⟨a₂, ha₂, c, hcCE, hhxc⟩ :=
      sec8sau_mem_sup_mul (E := E) (t := t) h.2
    have ha₂X : a₂ ∈ X := ha₂.1
    have ha₂Ct : a₂ ∈ Ct := ha₂.2
    have hcB : ∀ b ∈ B, c * b = b * c := by
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp hcCE b (hBE hb)).symm
    have hcBinv : ∀ b ∈ B, c⁻¹ * b = b * c⁻¹ := by
      intro b hb
      calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcB b hb]
        _ = b * c⁻¹ := by group
    have hx_eq : a₂ = (h : G) * c⁻¹ := by rw [hhxc]; group
    have hxB : ∀ b ∈ B, a₂ * b = b * a₂ := by
      intro b hb
      calc a₂ * b = ((h : G) * c⁻¹) * b := by rw [hx_eq]
        _ = (h : G) * (c⁻¹ * b) := by group
        _ = (h : G) * (b * c⁻¹) := by rw [hcBinv b hb]
        _ = ((h : G) * b) * c⁻¹ := by group
        _ = (b * (h : G)) * c⁻¹ := by rw [hcommB ⟨b, hb⟩]
        _ = b * ((h : G) * c⁻¹) := by group
        _ = b * a₂ := by rw [hx_eq]
    have hAle : A ≤ centralizer ({a₂} : Set G) := by
      change zpowers t ⊔ B ≤ centralizer ({a₂} : Set G)
      refine sup_le ?_ ?_
      · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp ha₂Ct).symm
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hxB b hb).symm
    have hxA : a₂ ∈ centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAle ha)
    have hxAO : a₂ ∈ A ⊔ O := by rw [← hcentA]; exact hxA
    have hcommAO : ∀ a ∈ A, ∀ o ∈ O, a * o = o * a := by
      intro a ha o ho
      exact Subgroup.mem_centralizer_iff.mp (hOleCentA ho) a ha
    obtain ⟨a₃, ha₃A, o, hoO, ha₂ao⟩ := exists_mul_of_mem_sup_of_commute hcommAO hxAO
    have ho_eq : o = a₃⁻¹ * a₂ := by rw [ha₂ao]; group
    have hoX : o ∈ X := by
      rw [ho_eq]
      exact X.mul_mem (X.inv_mem (hAX ha₃A)) ha₂X
    have htA : t ∈ A := by
      change t ∈ zpowers t ⊔ B
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have ho_t : o * t = t * o :=
      (Subgroup.mem_centralizer_iff.mp (hOleCentA hoO) t htA).symm
    have ho_B : ∀ b ∈ B, o * b = b * o := by
      intro b hb
      have hbA : b ∈ A := by
        change b ∈ zpowers t ⊔ B
        exact Subgroup.mem_sup_right hb
      exact (Subgroup.mem_centralizer_iff.mp (hOleCentA hoO) b hbA).symm
    have ho_odd : Odd (orderOf o) := odd_orderOf_of_mem_oddCoreIn hoO
    have hoCE : o ∈ CE := sec8s_odd_cent_E hE ho_odd hoX ho_t ho_B
    have hCEK : CE ≤ K := by change CE ≤ zpowers t ⊔ CE; exact le_sup_right
    have hhK : (h : G) ∈ K := by
      have h1 : (h : G) = a₃ * o * c := by rw [hhxc, ha₂ao]
      rw [h1]
      exact K.mul_mem (K.mul_mem (hAK ha₃A) (hCEK hoCE)) (hCEK hcCE)
    exact hhK
  have hker_ge : K.subgroupOf H ≤ φ.ker := by
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [hphi_apply]
    change (h : G) * (b : G) * (h : G)⁻¹ = (b : G)
    have hKCB : K ≤ centralizer (B : Set G) := by
      change zpowers t ⊔ CE ≤ centralizer (B : Set G)
      refine sup_le ?_ ?_
      · rw [zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mp (hBCt hb)
      · exact Subgroup.centralizer_le hBE
    have hbcomm : (h : G) * (b : G) = (b : G) * (h : G) :=
      (Subgroup.mem_centralizer_iff.mp (hKCB hh) b b.2).symm
    calc (h : G) * (b : G) * (h : G)⁻¹ = ((b : G) * (h : G)) * (h : G)⁻¹ := by rw [hbcomm]
      _ = (b : G) := by group
  exact ⟨φ, hsurj, le_antisymm hker_le hker_ge⟩

end CFSG.OddStandard.SmallF3.Omega