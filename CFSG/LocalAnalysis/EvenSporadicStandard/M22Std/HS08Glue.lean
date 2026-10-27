module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Pi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsBeta

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] noncomputable def hs08QuotAut {L : Type*} [Group L] (M : Subgroup L)
    [M.Characteristic] : MulAut L →* MulAut (L ⧸ M) where
  toFun φ := QuotientGroup.congr M M φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def hs08Act (H : Subgroup G) (hH : H ≤ normalizer (L : Set G)) :
    H →* MulAut (L ⧸ center L) :=
  (hs08QuotAut (center L)).comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hH))

theorem hs08Act_mk (H : Subgroup G) (hH : H ≤ normalizer (L : Set G)) (h : H) (l : L) :
    hs08Act H hH h (l : L ⧸ center L) =
      ((⟨(h : G) * l * (h : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hH h.2) l).1 l.2⟩ : L) :
        L ⧸ center L) := rfl

@[expose] noncomputable def hs08Pi (H : Subgroup G) (hH : H ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* Carrier .M22) : H →* MulAut (Carrier .M22) :=
  (MulAut.congr e).toMonoidHom.comp (hs08Act H hH)

theorem hs08Pi_apply (H : Subgroup G) (hH : H ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* Carrier .M22) (h : H) (q : L ⧸ center L) :
    hs08Pi H hH e h (e q) = e (hs08Act H hH h q) := by
  simp [hs08Pi, MulAut.congr_apply]

theorem hs08_t_mem' (t : G) : t ∈ centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem hs08_eq_one_or_eq {t x : G} (hx : x ∈ zpowers t) (htt : t * t = 1) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, ht2, one_zpow, one_mul]

theorem hs08_conj_injective :
    Function.Injective (MulAut.conj : Carrier .M22 →* MulAut (Carrier .M22)) := fun a b hab =>
  tab_injective (by rw [← autTab_conj, ← autTab_conj, hab])

section Main

variable {t : G} (hc : CoverSetting L t)

include hc

theorem hs08_le_normalizer : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  le_of_eq hc.centralizer_t

variable [Group.IsPerfect L] (e : L ⧸ center L ≃* Carrier .M22)

noncomputable abbrev hs08PiOf : centralizer ({t} : Set G) →* MulAut (Carrier .M22) :=
  hs08Pi (centralizer ({t} : Set G)) (hs08_le_normalizer hc) e

omit [Group.IsPerfect L] in
theorem hs08PiOf_of_mem (l : L) :
    hs08PiOf hc e ⟨(l : G), hc.le_centralizer l.2⟩ = MulAut.conj (e (l : L ⧸ center L)) := by
  ext y
  obtain ⟨q, rfl⟩ := e.surjective y
  obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q
  rw [hs08Pi_apply, hs08Act_mk, MulAut.conj_apply]
  have : ((⟨(l : G) * l' * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.1
      (hs08_le_normalizer hc (hc.le_centralizer l.2)) l').1 l'.2⟩ : L) : L ⧸ center L) =
      (l : L ⧸ center L) * (l' : L ⧸ center L) * (l : L ⧸ center L)⁻¹ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  rw [this, map_mul, map_mul, map_inv]

omit [Group.IsPerfect L] in
theorem hs08PiOf_eq_one_iff (h : centralizer ({t} : Set G)) :
    hs08PiOf hc e h = 1 ↔ ∀ l : L, hs08Act (centralizer ({t} : Set G)) (hs08_le_normalizer hc) h
      (l : L ⧸ center L) = (l : L ⧸ center L) := by
  constructor
  · intro h1 l
    have := congrArg (fun φ : MulAut (Carrier .M22) => φ (e (l : L ⧸ center L))) h1
    simp only [MulAut.one_apply] at this
    exact e.injective (by rwa [hs08Pi_apply] at this)
  · intro h1
    ext y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hs08Pi_apply, h1 l, MulAut.one_apply]

theorem hs08PiOf_centralizes (h : centralizer ({t} : Set G)) (h1 : hs08PiOf hc e h = 1) :
    ∀ l : L, (h : G) * l = l * (h : G) := by
  have hmem := hs08_le_normalizer hc h.2
  set σ : MulAut L := L.normalizerMonoidHom ⟨(h : G), hmem⟩ with hσ
  have hσl : ∀ l : L, ((σ l : L) : G) = (h : G) * l * (h : G)⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(h : G), hmem⟩ l
  have hcen : ∀ l : L, σ l * l⁻¹ ∈ center L := by
    intro l
    have h2 := (hs08PiOf_eq_one_iff hc e h).1 h1 l
    have h3 : ((σ l : L) : L ⧸ center L) = (l : L ⧸ center L) := h2
    have := (QuotientGroup.eq_iff_div_mem).1 h3
    simpa [div_eq_mul_inv] using this
  have hmul : ∀ a b : L, σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
    intro a b
    have hc2 := Subgroup.mem_center_iff.1 (hcen b) a
    calc σ (a * b) * (a * b)⁻¹ = σ a * σ b * b⁻¹ * a⁻¹ := by rw [map_mul]; group
      _ = (σ a * a⁻¹) * (a * (σ b * b⁻¹) * a⁻¹) := by group
      _ = (σ a * a⁻¹) * ((σ b * b⁻¹) * a * a⁻¹) := by rw [hc2]
      _ = (σ a * a⁻¹) * (σ b * b⁻¹) := by group
  let f : L →* L := MonoidHom.mk' (fun l => σ l * l⁻¹) hmul
  have hcomm : commutator L ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have ha := Subgroup.mem_center_iff.1 (hcen a)
    simp only [f, MonoidHom.mk'_apply]
    rw [commutatorElement_def]
    have hb := (Subgroup.mem_center_iff.1 (hcen b)) (σ a * a⁻¹)
    rw [hb]
    group
  have hperf : commutator L = ⊤ := Group.isPerfect_def.1 inferInstance
  intro l
  have h4 : l ∈ f.ker := hcomm (hperf ▸ Subgroup.mem_top l)
  have h5 : σ l * l⁻¹ = 1 := h4
  have h6 : σ l = l := mul_inv_eq_one.1 h5
  have h7 := hσl l
  rw [h6] at h7
  calc (h : G) * l = ((h : G) * l * (h : G)⁻¹) * h := by group
    _ = l * h := by rw [← h7]

theorem hs08PiOf_ker (x : centralizer ({t} : Set G)) :
    hs08PiOf hc e x = 1 ↔ (x = 1 ∨ x = ⟨t, hs08_t_mem' t⟩) := by
  constructor
  · intro h1
    have hcent := hs08PiOf_centralizes hc e x h1
    have hxC : (x : G) ∈ centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun l hl => (hcent ⟨l, hl⟩).symm
    rw [hc.centralizer_L] at hxC
    rcases hs08_eq_one_or_eq hxC hc.mul_self_t with h2 | h2
    · left; exact Subtype.ext h2
    · right; exact Subtype.ext h2
  · rintro (rfl | rfl)
    · exact map_one _
    · refine (hs08PiOf_eq_one_iff hc e _).2 fun l => ?_
      have hcomm : t * (l : G) = l * t :=
        (Subgroup.mem_centralizer_iff.1 hc.t_mem_centralizer l l.2).symm
      have : (⟨t * (l : G) * t⁻¹, (Subgroup.mem_normalizer_iff.1
          (hs08_le_normalizer hc (hs08_t_mem' t)) l).1 l.2⟩ : L) = l := by
        apply Subtype.ext
        simp only
        rw [hcomm]; group
      exact congrArg (fun q : L => (q : L ⧸ center L)) this

theorem hs08PiOf_inner_iff (x : centralizer ({t} : Set G)) :
    hs08PiOf hc e x ∈ innerImage (Carrier .M22) ⊤ ↔ (x : G) ∈ L := by
  constructor
  · intro hin
    obtain ⟨y₀, -, hy₀⟩ := Subgroup.mem_map.1 hin
    obtain ⟨q, hq⟩ := e.surjective y₀
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : hs08PiOf hc e x = hs08PiOf hc e ⟨(l : G), hc.le_centralizer l.2⟩ := by
      rw [hs08PiOf_of_mem hc e l, hq, hy₀]
    have h2 : hs08PiOf hc e (⟨(l : G), hc.le_centralizer l.2⟩⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, ← h1, inv_mul_cancel]
    rcases (hs08PiOf_ker hc e _).1 h2 with h3 | h3
    · have : (x : G) = l := by
        have := congrArg Subtype.val h3
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one] at this
        rw [inv_mul_eq_one] at this
        exact this.symm
      rw [this]; exact l.2
    · have : (x : G) = l * t := by
        have := congrArg Subtype.val h3
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at this
        calc (x : G) = (l : G) * ((l : G)⁻¹ * x) := by group
          _ = l * t := by rw [this]
      rw [this]
      exact L.mul_mem l.2 hc.t_mem
  · intro hx
    have := hs08PiOf_of_mem hc e ⟨(x : G), hx⟩
    have hxe : (⟨(x : G), hc.le_centralizer hx⟩ : centralizer ({t} : Set G)) = x := Subtype.ext rfl
    rw [hxe] at this
    rw [this]
    exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩

theorem hs08_piData
    [Finite G] (hq : IsSporadic (L ⧸ center L) .M22) {y : G}
    (hy : y ∈ centralizer ({t} : Set G)) (hyL : y ∉ L) (hy2 : y * y = 1) :
    PiData (hs08PiOf hc e) ⟨t, hs08_t_mem' t⟩ := by
  have hcov := hc.isM22Cover hq
  have hinj := hs08_conj_injective
  have hLH := hc.le_centralizer
  refine ⟨Subtype.ext hc.mul_self_t, fun h => hc.t_ne_one (congrArg Subtype.val h),
    fun x => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2).symm, ?_,
    hs08PiOf_ker hc e, ?_, ?_, ?_⟩
  ·
    set K := (hs08PiOf hc e).range with hK
    have hInn : innerImage (Carrier .M22) ⊤ ≤ K := by
      intro α hα
      obtain ⟨y₀, -, rfl⟩ := Subgroup.mem_map.1 hα
      obtain ⟨q, rfl⟩ := e.surjective y₀
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨⟨(l : G), hLH l.2⟩, hs08PiOf_of_mem hc e l⟩
    have hyK : hs08PiOf hc e ⟨y, hy⟩ ∈ K := ⟨⟨y, hy⟩, rfl⟩
    have hyo : hs08PiOf hc e ⟨y, hy⟩ ∉ innerImage (Carrier .M22) ⊤ := fun hin =>
      hyL ((hs08PiOf_inner_iff hc e ⟨y, hy⟩).1 hin)
    have h1 := Subgroup.relIndex_mul_index hInn
    rw [index_innerImage_top] at h1
    have hKidx : K.index = 1 := by
      have hdvd : K.index ∣ 2 := ⟨(innerImage (Carrier .M22) ⊤).relIndex K, by rw [← h1, mul_comm]⟩
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        have h3 : (innerImage (Carrier .M22) ⊤).relIndex K = 1 := by omega
        have := Subgroup.relIndex_eq_one.1 h3
        exact hyo (this hyK)
    have hKtop : K = ⊤ := Subgroup.index_eq_one.1 hKidx
    intro α
    have : α ∈ K := hKtop ▸ Subgroup.mem_top α
    exact this
  ·
    intro x hin hsq
    have hxL : (x : G) ∈ L := (hs08PiOf_inner_iff hc e x).1 hin
    set l : L := ⟨(x : G), hxL⟩ with hl
    have hxl : x = ⟨(l : G), hLH l.2⟩ := Subtype.ext rfl
    have hπ : hs08PiOf hc e x = MulAut.conj (e (l : L ⧸ center L)) := by
      rw [hxl]; exact hs08PiOf_of_mem hc e l
    have h1 : e (l : L ⧸ center L) * e (l : L ⧸ center L) = 1 := by
      apply hinj
      rw [hπ] at hsq
      rw [map_mul, map_one]
      exact hsq
    have h2 : (l : L ⧸ center L) * (l : L ⧸ center L) = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact h1
    have : l * l = 1 := by
      by_cases hl1 : (l : L ⧸ center L) = 1
      · rcases hcov.eq_one_or_eq_t_of_mk_eq_one hl1 with h3 | h3
        · rw [h3, one_mul]
        · rw [h3]; exact Subtype.ext hc.mul_self_t
      · refine hcov.mul_self_of_lift (orderOf_eq_prime ?_ hl1)
        rw [sq]; exact h2
    apply Subtype.ext
    have h' : (l : G) * (l : G) = 1 := by simpa using congrArg Subtype.val this
    simpa [hl] using h'
  ·
    intro u hin hsq hne
    have huL : (u : G) ∈ L := (hs08PiOf_inner_iff hc e u).1 hin
    set l : L := ⟨(u : G), huL⟩ with hl
    have hxl : u = ⟨(l : G), hLH l.2⟩ := Subtype.ext rfl
    have hπ : hs08PiOf hc e u = MulAut.conj (e (l : L ⧸ center L)) := by
      rw [hxl]; exact hs08PiOf_of_mem hc e l
    have h1 : e (l : L ⧸ center L) * e (l : L ⧸ center L) = 1 := by
      apply hinj
      rw [hπ] at hsq
      rw [map_mul, map_one]
      exact hsq
    have h2 : (l : L ⧸ center L) * (l : L ⧸ center L) = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact h1
    have hl1 : (l : L ⧸ center L) ≠ 1 := by
      intro h3
      apply hne
      rw [hπ, h3, map_one, map_one]
    obtain ⟨w, hw⟩ := hcov.exists_sq_of_lift l (orderOf_eq_prime (by rw [sq]; exact h2) hl1)
    refine ⟨⟨(w : G), hLH w.2⟩, Subtype.ext ?_⟩
    have h' : (w : G) * (w : G) = (l : G) := by simpa using congrArg Subtype.val hw
    simpa [hl] using h'
  · refine ⟨⟨y, hy⟩, fun hin => hyL ((hs08PiOf_inner_iff hc e ⟨y, hy⟩).1 hin), Subtype.ext hy2⟩

end Main

end CFSG.EvenSporadicStandard.M22Std
