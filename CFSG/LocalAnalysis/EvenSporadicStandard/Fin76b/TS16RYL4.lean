module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z : G}

theorem s16LData_of_sigma [Finite G] {E : Subgroup G} {t β : G} (hTD : ThetaData G L z)
    (hz2 : z * z = 1) (hzL : z ∉ L)
    (htL : t ∈ L) (hβL : β ∈ L) (hE : E = (rootGroup ↥L ⟨t, htL⟩).map L.subtype)
    (hF1 : S16F1 ↥L) {r : MulAut ↥L} {v' ξ' : ↥L}
    (hrel : S16Rel (⟨t, htL⟩ : ↥L) ⟨β, hβL⟩ r v' ξ') (σ' : ↥(centralizer ({z} : Set G)))
    (hσθ : hTD.theta σ' = r) (hσ2 : (σ' : G) * σ' = 1) (hσnotL : (σ' : G) ∉ L ⊔ zpowers z) :
    S16LData G L z t β E σ' v' ξ' := by
  classical
  have hact : ∀ ℓ : ↥L, (σ' : G) * ℓ * (σ' : G)⁻¹ = ((r ℓ : ↥L) : G) := hTD.theta_eq_iff.1 hσθ
  set σ : G := (σ' : G) with hσdef
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set β' : ↥L := ⟨β, hβL⟩ with hβ'
  set Er : Subgroup ↥L := rootGroup ↥L t' with hEr
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσz : σ * z = z * σ := mem_centralizer_singleton_iff.1 σ'.2
  have hσL : ∀ ℓ ∈ L, σ * ℓ * σ⁻¹ ∈ L := fun ℓ hℓ => hTD.norm σ σ'.2 ℓ hℓ
  have hE1 : ∀ y ∈ Er, σ * (y : G) * σ⁻¹ ∈ E := by
    intro y hy
    rw [hE, hact y]
    exact ⟨r y, rootGroup_stable r hrel.r_t y hy, rfl⟩
  have hσE : σ ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [hE] at he
      obtain ⟨y, hy, rfl⟩ := he
      exact hE1 y hy
    · intro he
      have h2 : σ * (σ * e * σ⁻¹) * σ⁻¹ = e := by
        calc σ * (σ * e * σ⁻¹) * σ⁻¹ = (σ * σ) * e * (σ⁻¹ * σ⁻¹) := by group
          _ = e := by rw [hσ2, hσinv, hσ2]; group
      rw [hE] at he ⊢
      obtain ⟨y, hy, hye⟩ := he
      refine ⟨r y, rootGroup_stable r hrel.r_t y hy, ?_⟩
      calc ((r y : ↥L) : G) = σ * (y : G) * σ⁻¹ := (hact y).symm
        _ = σ * (σ * e * σ⁻¹) * σ⁻¹ := by
          have : (y : G) = σ * e * σ⁻¹ := hye
          rw [this]
        _ = e := h2
  have hmapCE : (Er ⊓ fixedSub r).map L.subtype = E ⊓ centralizer ({σ} : Set G) := by
    ext e
    constructor
    · rintro ⟨y, ⟨hyE, hyf⟩, rfl⟩
      refine ⟨by rw [hE]; exact ⟨y, hyE, rfl⟩, ?_⟩
      show (y : G) ∈ centralizer ({σ} : Set G)
      rw [mem_centralizer_singleton_iff]
      have h1 : σ * (y : G) * σ⁻¹ = y := by rw [hact y, show r y = y from hyf]
      calc (y : G) * σ = (σ * y * σ⁻¹) * σ := by rw [h1]
        _ = σ * y := by group
    · rintro ⟨he, hc⟩
      rw [hE] at he
      obtain ⟨y, hy, rfl⟩ := he
      have hc' := mem_centralizer_singleton_iff.1 hc
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      show r y = y
      apply Subtype.ext
      rw [← hact y]
      have hc'' : (y : G) * σ = σ * (y : G) := hc'
      calc σ * (y : G) * σ⁻¹ = ((y : G) * σ) * σ⁻¹ := by rw [hc'']
        _ = y := by group
  have hcardCE : Nat.card ↥(E ⊓ centralizer ({σ} : Set G)) = 8 := by
    calc Nat.card ↥(E ⊓ centralizer ({σ} : Set G)) =
          Nat.card ↥((Er ⊓ fixedSub r).map L.subtype) := by rw [hmapCE]
      _ = Nat.card ↥(Er ⊓ fixedSub r) := Subgroup.card_map_of_injective L.subtype_injective
      _ = 8 := hrel.card_CE
  have hCEeq : closure ({(v' : G) * v', (v' : G) * ξ'} : Set G) =
      E ⊓ centralizer ({σ} : Set G) := by
    rw [← hmapCE, ← hrel.CE_eq, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨v' * v', Or.inl rfl, rfl⟩
      · exact ⟨v' * ξ', Or.inr rfl, rfl⟩
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · left; rfl
      · right; rfl
  have hvH : (v' : G) ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (hTD.z_cent _ v'.2)
  have hξH : (ξ' : G) ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (hTD.z_cent _ ξ'.2)
  set vH : ↥(centralizer ({z} : Set G)) := ⟨v', hvH⟩ with hvH_def
  set ξH : ↥(centralizer ({z} : Set G)) := ⟨ξ', hξH⟩ with hξH_def
  set Y'' : Subgroup ↥(centralizer ({z} : Set G)) := closure ({vH, ξH, σ'} : Set _) with hY''
  have hY''map : Y''.map hTD.theta =
      closure ({MulAut.conj v', MulAut.conj ξ', r} : Set (MulAut ↥L)) := by
    rw [hY'', MonoidHom.map_closure]
    congr 1
    ext φ
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, (rfl | rfl | rfl), rfl⟩
      · left; exact hTD.theta_of_mem v'.2 hvH
      · right; left; exact hTD.theta_of_mem ξ'.2 hξH
      · right; right; exact hσθ
    · rintro (rfl | rfl | rfl)
      · exact ⟨vH, Or.inl rfl, hTD.theta_of_mem v'.2 hvH⟩
      · exact ⟨ξH, Or.inr (Or.inl rfl), hTD.theta_of_mem ξ'.2 hξH⟩
      · exact ⟨σ', Or.inr (Or.inr rfl), hσθ⟩
  have hY''le : ∀ y ∈ Y'', ((y : ↥(centralizer ({z} : Set G))) : G) ∈ L ⊔ zpowers σ := by
    intro y hy
    have : Y'' ≤ (L ⊔ zpowers σ).comap (centralizer ({z} : Set G)).subtype := by
      rw [hY'', Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact mem_sup_left v'.2
      · exact mem_sup_left ξ'.2
      · exact mem_sup_right (mem_zpowers σ)
    exact this hy
  have hY''inj : Function.Injective (hTD.theta.comp Y''.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have := hTD.theta_injOn hz2 hzL σ'.2 hσ2 hσnotL (g := (y : ↥(centralizer ({z} : Set G))))
      (hY''le y y.2) hy
    exact Subtype.ext (Subtype.ext this)
  have hcardY : Nat.card ↥(closure ({(v' : G), (ξ' : G), σ} : Set G)) = 32 := by
    have h1 : closure ({(v' : G), (ξ' : G), σ} : Set G) =
        Y''.map (centralizer ({z} : Set G)).subtype := by
      rw [hY'', MonoidHom.map_closure]
      congr 1
      ext g
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨vH, Or.inl rfl, rfl⟩
        · exact ⟨ξH, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨σ', Or.inr (Or.inr rfl), rfl⟩
      · rintro ⟨x, (rfl | rfl | rfl), rfl⟩
        · left; rfl
        · right; left; rfl
        · right; right; rfl
    rw [h1, Subgroup.card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
      Nat.card_congr (MonoidHom.ofInjective hY''inj).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype, hY''map]
    exact hrel.card_Y
  refine
  { σ_z := hσz
    σ_sq := hσ2
    σ_notL := hσnotL
    σ_L := hσL
    v_L := v'.2
    ξ_L := ξ'.2
    v_t := congrArg Subtype.val hrel.v_t
    ξ_t := congrArg Subtype.val hrel.ξ_t
    v4 := by simpa using congrArg Subtype.val hrel.v4
    v8 := by simpa using congrArg Subtype.val hrel.v8
    ξ_sq := congrArg Subtype.val hrel.ξ_sq
    ξ_ne_one := fun h => hrel.ξ_ne_one (Subtype.ext h)
    ξ_ne_t := fun h => hrel.ξ_ne_t (Subtype.ext h)
    ξ_v := congrArg Subtype.val hrel.ξ_v
    σ_t := by rw [hact t', hrel.r_t]
    σ_v := by rw [hact v', hrel.r_v]; rfl
    σ_ξ := by rw [hact ξ', hrel.r_ξ]; rfl
    v_β := congrArg Subtype.val hrel.v_β
    ξ_β := congrArg Subtype.val hrel.ξ_β
    σ_β := by rw [hact β', hrel.r_β]; rfl
    σ_E := hσE
    card_CE := hcardCE
    CE_eq := hCEeq
    card_Y := hcardY
    V0 := ?_
    rank5 := ?_ }
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨V0', hV0', ⟨eV⟩, m, hm, hcard⟩ := hF1 r hrel.r_sq hrel.r_outer
    have hmapfix : (fixedSub r).map L.subtype = L ⊓ centralizer ({σ} : Set G) := by
      ext e
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        show (y : G) ∈ centralizer ({σ} : Set G)
        rw [mem_centralizer_singleton_iff]
        have h1 : σ * (y : G) * σ⁻¹ = y := by rw [hact y, show r y = y from hy]
        calc (y : G) * σ = (σ * y * σ⁻¹) * σ := by rw [h1]
          _ = σ * y := by group
      · rintro ⟨he, hc⟩
        have hc' : e * σ = σ * e := mem_centralizer_singleton_iff.1 hc
        refine ⟨⟨e, he⟩, ?_, rfl⟩
        show r ⟨e, he⟩ = ⟨e, he⟩
        apply Subtype.ext
        rw [← hact ⟨e, he⟩]
        show σ * e * σ⁻¹ = e
        calc σ * e * σ⁻¹ = (e * σ) * σ⁻¹ := by rw [hc']
          _ = e := by group
    have hV0card : Nat.card ↥(V0'.map L.subtype) = 16 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective,
        Nat.card_congr eV.toEquiv, DihedralGroup.nat_card]
    refine ⟨V0'.map L.subtype, ?_, ?_, ?_, ⟨(V0'.equivMapOfInjective L.subtype
      L.subtype_injective).symm.trans eV⟩⟩
    · rw [← hmapfix]
      exact Subgroup.map_mono hV0'
    · exact IsPGroup.of_card (n := 4) (by rw [hV0card]; norm_num)
    · intro R hR hRle hVR
      have hdvd : Nat.card ↥R ∣ 16 * m := by
        have h1 : Nat.card ↥R ∣ Nat.card ↥(L ⊓ centralizer ({σ} : Set G)) :=
          Subgroup.card_dvd_of_le hRle
        rw [← hmapfix, Subgroup.card_map_of_injective L.subtype_injective, hcard] at h1
        exact h1
      obtain ⟨k, hk⟩ := hR.exists_card_eq
      have hcop : Nat.Coprime (Nat.card ↥R) m := by
        rw [hk]
        exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
      have h16 : Nat.card ↥R ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd
      have hle16 : Nat.card ↥R ≤ 16 := Nat.le_of_dvd (by norm_num) h16
      exact (Subgroup.eq_of_le_of_card_ge hVR (by rw [hV0card]; exact hle16)).symm.le
  · obtain ⟨C, hCΘ, htC, hξC, hCc, hCcard, hCsq, hCcomm⟩ := hrel.rank5
    set A : Subgroup G := L ⊓ centralizer ({t} : Set G) with hA
    have hAH : ∀ a ∈ A, a ∈ centralizer ({z} : Set G) := fun a ha =>
      mem_centralizer_singleton_iff.2 (hTD.z_cent a ha.1)
    set N'' : Subgroup ↥(centralizer ({z} : Set G)) :=
      A.subgroupOf (centralizer ({z} : Set G)) ⊔ zpowers σ' with hN''
    have hN''le : ∀ g ∈ N'', ((g : ↥(centralizer ({z} : Set G))) : G) ∈ A ⊔ zpowers σ := by
      intro g hg
      have : N'' ≤ (A ⊔ zpowers σ).comap (centralizer ({z} : Set G)).subtype := by
        refine sup_le (fun a ha => ?_) ?_
        · exact mem_sup_left (Subgroup.mem_subgroupOf.1 ha)
        · rw [zpowers_le]
          exact mem_sup_right (mem_zpowers σ)
      exact this hg
    have hLσ : ∀ g ∈ N'', ((g : ↥(centralizer ({z} : Set G))) : G) ∈ L ⊔ zpowers σ := by
      intro g hg
      exact (sup_le_sup_right (inf_le_left : A ≤ L) _ : A ⊔ zpowers σ ≤ L ⊔ zpowers σ)
        (hN''le g hg)
    have hθN : Function.Injective (hTD.theta.comp N''.subtype) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have := hTD.theta_injOn hz2 hzL σ'.2 hσ2 hσnotL
        (g := ((g : ↥N'') : ↥(centralizer ({z} : Set G)))) (hLσ g g.2) hg
      exact Subtype.ext (Subtype.ext this)
    have htA : t ∈ A := ⟨htL, mem_centralizer_singleton_iff.2 rfl⟩
    have hξA : (ξ' : G) ∈ A :=
      ⟨ξ'.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hrel.ξ_t)⟩
    have hAN : ∀ a (ha : a ∈ A), (⟨a, hAH a ha⟩ : ↥(centralizer ({z} : Set G))) ∈ N'' :=
      fun a ha => mem_sup_left (Subgroup.mem_subgroupOf.2 ha)
    set gt : ↥N'' := ⟨⟨t, hAH t htA⟩, hAN t htA⟩ with hgt
    set gξ : ↥N'' := ⟨⟨ξ', hAH ξ' hξA⟩, hAN ξ' hξA⟩ with hgξ
    have hθt : (hTD.theta.comp N''.subtype) gt = MulAut.conj t' :=
      hTD.theta_of_mem htL (hAH t htA)
    have hθξ : (hTD.theta.comp N''.subtype) gξ = MulAut.conj ξ' :=
      hTD.theta_of_mem ξ'.2 (hAH _ hξA)
    have hΘ : thetaSub t' r ≤ (hTD.theta.comp N''.subtype).range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨e, he, rfl⟩
        have he' : (e : G) ∈ A := ⟨e.2, mem_centralizer_singleton_iff.2 (by
          have := mem_centralizer_singleton_iff.1 he
          exact congrArg Subtype.val this)⟩
        refine ⟨⟨⟨e, hAH e he'⟩, hAN e he'⟩, ?_⟩
        exact hTD.theta_of_mem e.2 (hAH e he')
      · rw [zpowers_le]
        exact ⟨⟨σ', mem_sup_right (mem_zpowers σ')⟩, hσθ⟩
    have hCrange : C ≤ (hTD.theta.comp N''.subtype).range := hCΘ.trans hΘ
    set Ĉ'' : Subgroup ↥N'' := C.comap (hTD.theta.comp N''.subtype) with hĈ''
    have hmapĈ : Ĉ''.map (hTD.theta.comp N''.subtype) = C := by
      rw [hĈ'', Subgroup.map_comap_eq]
      exact inf_eq_right.2 hCrange
    have hcardĈ'' : Nat.card ↥Ĉ'' = 32 := by
      calc Nat.card ↥Ĉ'' = Nat.card ↥(Ĉ''.map (hTD.theta.comp N''.subtype)) :=
            (Subgroup.card_map_of_injective hθN).symm
        _ = Nat.card ↥C := by rw [hmapĈ]
        _ = 32 := hCcard
    have hι : Function.Injective ((centralizer ({z} : Set G)).subtype.comp N''.subtype) :=
      (centralizer ({z} : Set G)).subtype_injective.comp N''.subtype_injective
    have hconjφ : ∀ (φ : MulAut ↥L) (x : ↥L), φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
      intro φ x
      ext y
      simp [MulAut.conj_apply]
    have hback : ∀ g g' : ↥N'', (hTD.theta.comp N''.subtype) g = (hTD.theta.comp N''.subtype) g' →
        ((g : ↥(centralizer ({z} : Set G))) : G) = ((g' : ↥(centralizer ({z} : Set G))) : G) :=
      fun g g' h => congrArg (fun x : ↥N'' => ((x : ↥(centralizer ({z} : Set G))) : G)) (hθN h)
    refine ⟨Ĉ''.map ((centralizer ({z} : Set G)).subtype.comp N''.subtype), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact hN''le g g.2
    · rintro _ ⟨g, hg, rfl⟩
      have hφ : (hTD.theta.comp N''.subtype) g ∈ centralizer ({MulAut.conj ξ'} : Set (MulAut ↥L)) :=
        hCc hg
      have hφ' := mem_centralizer_singleton_iff.1 hφ
      have h1 : MulAut.conj ((hTD.theta.comp N''.subtype) g ξ') = MulAut.conj ξ' := by
        rw [← hconjφ, hφ']
        group
      have h2 : (hTD.theta.comp N''.subtype) g ξ' = ξ' := conj_injective_of_center hTD h1
      have h3 := hTD.theta_apply (g : ↥(centralizer ({z} : Set G))) ξ'
      have h4 : ((g : ↥(centralizer ({z} : Set G))) : G) * ξ' *
          ((g : ↥(centralizer ({z} : Set G))) : G)⁻¹ = ξ' := by
        rw [← h3]
        exact congrArg Subtype.val h2
      rw [mem_centralizer_singleton_iff]
      show ((g : ↥(centralizer ({z} : Set G))) : G) * ξ' = ξ' * ((g : ↥(centralizer ({z} : Set G))) : G)
      calc ((g : ↥(centralizer ({z} : Set G))) : G) * ξ' =
          (((g : ↥(centralizer ({z} : Set G))) : G) * ξ' *
            ((g : ↥(centralizer ({z} : Set G))) : G)⁻¹) *
            ((g : ↥(centralizer ({z} : Set G))) : G) := by group
        _ = ξ' * ((g : ↥(centralizer ({z} : Set G))) : G) := by rw [h4]
    · refine ⟨gt, ?_, rfl⟩
      show (hTD.theta.comp N''.subtype) gt ∈ C
      rw [hθt]; exact htC
    · refine ⟨gξ, ?_, rfl⟩
      show (hTD.theta.comp N''.subtype) gξ ∈ C
      rw [hθξ]; exact hξC
    · rw [Subgroup.card_map_of_injective hι]
      exact hcardĈ''
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : (hTD.theta.comp N''.subtype) (g * g) ∈ quadSet t' ξ' := by
        rw [map_mul]; exact hCsq _ hg
      simp only [quadSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h | h | h | h
      · left
        have := hback (g * g) 1 (by rw [h, map_one])
        simpa using this
      · right; left
        have := hback (g * g) gt (by rw [h, hθt])
        simpa using this
      · right; right; left
        have := hback (g * g) gξ (by rw [h, hθξ])
        simpa using this
      · right; right; right
        have := hback (g * g) (gt * gξ) (by rw [h, map_mul, hθt, hθξ])
        simpa using this
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨h', hh, rfl⟩
      have h1 : (hTD.theta.comp N''.subtype) (g * h' * g⁻¹ * h'⁻¹) ∈ quadSet t' ξ' := by
        simp only [map_mul, map_inv]; exact hCcomm _ hg _ hh
      simp only [quadSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h | h | h | h
      · left
        have := hback (g * h' * g⁻¹ * h'⁻¹) 1 (by rw [h, map_one])
        simpa using this
      · right; left
        have := hback (g * h' * g⁻¹ * h'⁻¹) gt (by rw [h, hθt])
        simpa using this
      · right; right; left
        have := hback (g * h' * g⁻¹ * h'⁻¹) gξ (by rw [h, hθξ])
        simpa using this
      · right; right; right
        have := hback (g * h' * g⁻¹ * h'⁻¹) (gt * gξ) (by rw [h, map_mul, hθt, hθξ])
        simpa using this

theorem exists_s16LData [Finite G] {E : Subgroup G} {t β : G} (hTD : ThetaData G L z)
    (hz2 : z * z = 1) (hzL : z ∉ L) (hsq : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L)
    (htL : t ∈ L) (hβL : β ∈ L) (hE : E = (rootGroup ↥L ⟨t, htL⟩).map L.subtype)
    (hM : S16Model ↥L ⟨t, htL⟩ ⟨β, hβL⟩) (hF1 : S16F1 ↥L) :
    ∃ σ v ξ : G, S16LData G L z t β E σ v ξ ∧ S16LData G L z t β E (σ * z) v ξ := by
  obtain ⟨r, v', ξ', hrel⟩ := hM
  obtain ⟨σ', hσθ, hσ2, hσnotL⟩ := hTD.exists_sigma hz2 hzL hsq r hrel.r_sq hrel.r_outer
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  set σ'' : ↥(centralizer ({z} : Set G)) := σ' * ⟨z, hzH⟩ with hσ''
  refine ⟨σ', v', ξ', s16LData_of_sigma hTD hz2 hzL htL hβL hE hF1 hrel σ' hσθ hσ2 hσnotL, ?_⟩
  have hσz : (σ' : G) * z = z * σ' := mem_centralizer_singleton_iff.1 σ'.2
  have h1 : hTD.theta σ'' = r := by rw [hσ'', map_mul, hTD.theta_z, mul_one, hσθ]
  have h2 : ((σ'' : ↥(centralizer ({z} : Set G))) : G) * σ'' = 1 := by
    show (σ' : G) * z * ((σ' : G) * z) = 1
    calc (σ' : G) * z * ((σ' : G) * z) = (σ' * σ') * (z * z) := by
          calc (σ' : G) * z * ((σ' : G) * z) = (σ' : G) * (z * σ') * z := by group
            _ = (σ' : G) * (σ' * z) * z := by rw [hσz]
            _ = (σ' * σ') * (z * z) := by group
      _ = 1 := by rw [hσ2, hz2, one_mul]
  have h3 : ((σ'' : ↥(centralizer ({z} : Set G))) : G) ∉ L ⊔ zpowers z := by
    intro hmem
    apply hσnotL
    have : (σ' : G) = ((σ'' : ↥(centralizer ({z} : Set G))) : G) * z⁻¹ := by
      show (σ' : G) = σ' * z * z⁻¹
      group
    rw [this]
    exact mul_mem hmem (inv_mem (mem_sup_right (mem_zpowers z)))
  exact s16LData_of_sigma hTD hz2 hzL htL hβL hE hF1 hrel σ'' h1 h2 h3

end CFSG.EvenSporadicStandard.Fin76b
