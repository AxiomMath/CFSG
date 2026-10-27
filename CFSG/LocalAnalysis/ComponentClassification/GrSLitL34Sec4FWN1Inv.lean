module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN2
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.FW

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr GrS4
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem jq_eq_of_psi_eq {K M : Subgroup X} (hKM : K ≤ M) (hOKM : oddIn K ≤ oddIn M)
    {Q : Type*} [Group Q] {ψ : ↥K →* Q} (hψker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥K)
    {x x' : ↥K} (h : ψ x = ψ x') :
    L34Facts.jq M (inclusion hKM x) = L34Facts.jq M (inclusion hKM x') := by
  have h1 : x⁻¹ * x' ∈ pPrimeCore 2 ↥K := by
    rw [← hψker, map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((x⁻¹ * x' : ↥K) : X) ∈ oddIn M := hOKM ⟨_, h1, rfl⟩
  have h3 : L34Facts.jq M (inclusion hKM (x⁻¹ * x')) = 1 :=
    (L34Facts.mem_oddIn_iff (hKM (x⁻¹ * x').2)).mp h2
  rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h3
  exact h3

theorem psi_eq_one_of_jq_eq_one {K M : Subgroup X} (hKM : K ≤ M) {Q : Type*} [Group Q]
    {ψ : ↥K →* Q} (hψker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥K) {x : ↥K}
    (h : L34Facts.jq M (inclusion hKM x) = 1) : ψ x = 1 := by
  have h1 : (x : X) ∈ oddIn M := (L34Facts.mem_oddIn_iff (hKM x.2)).mpr h
  obtain ⟨o, ho, hox⟩ := GrS5.inf_oddIn_le_oddIn hKM (mem_inf.mpr ⟨h1, x.2⟩)
  have hox' : o = x := Subtype.ext hox
  rw [← hox']
  exact (hψker o).mpr ho

theorem psi_eq_one_of_commute {K M : Subgroup X} (hKM : K ≤ M)
    {ψ : ↥K →* Equiv.Perm (Fin 42)} (hψS : ∀ y, ψ y ∈ PSL3Four.S)
    (hψsurj : ∀ s ∈ PSL3Four.S, ∃ y, ψ y = s) (hψker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥K)
    {k₀ : ↥K} (h : ∀ k : ↥K,
      Commute (L34Facts.jq M (inclusion hKM k)) (L34Facts.jq M (inclusion hKM k₀))) :
    ψ k₀ = 1 := by
  have hc : ψ k₀ ∈ centralizer (PSL3Four.S : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, PSL3Four.S_le_R (hψS k₀)⟩
    obtain ⟨k, rfl⟩ := hψsurj s hs
    have h1 : L34Facts.jq M (inclusion hKM ⁅k, k₀⁆) = 1 := by
      rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (h k).eq
    have h2 := psi_eq_one_of_jq_eq_one hKM hψker h1
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  rw [PSL3Four.centralizer_S_inf_R, mem_bot] at hc
  exact hc

theorem exists_conj_jq_eq {K M : Subgroup X} (hKM : K ≤ M)
    (hOKM : oddIn K ≤ oddIn M) {ψ : ↥K →* Equiv.Perm (Fin 42)} (hψS : ∀ y, ψ y ∈ PSL3Four.S)
    (hψsurj : ∀ s ∈ PSL3Four.S, ∃ y, ψ y = s) (hψker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥K)
    {b k : ↥K} (hb2 : b * b = 1) (hb1 : b ≠ 1) (hk2 : ψ (k * k) = 1) :
    ∃ h : ↥K, L34Facts.jq M (inclusion hKM (h⁻¹ * k * h)) = 1 ∨
      L34Facts.jq M (inclusion hKM (h⁻¹ * k * h)) = L34Facts.jq M (inclusion hKM b) := by
  by_cases hk1 : ψ k = 1
  · refine ⟨1, Or.inl ?_⟩
    rw [inv_one, one_mul, mul_one,
      jq_eq_of_psi_eq hKM hOKM hψker (x' := 1) (by rw [hk1, map_one]), map_one, map_one]
  · have hψb : ψ b ≠ 1 := fun h => hb1 (eq_one_of_mem_pPrimeCore_of_two_pow ((hψker b).mp h)
      (n := 1) (by rw [pow_one, pow_two]; exact hb2))
    obtain ⟨σ, hσ⟩ := exists_conj_of_involution_S ⟨ψ k, hψS k⟩ ⟨ψ b, hψS b⟩
      (Subtype.ext (show ψ k * ψ k = 1 by rw [← map_mul]; exact hk2))
      (Subtype.ext (show ψ b * ψ b = 1 by rw [← map_mul, hb2, map_one]))
      (fun h => hk1 (congrArg Subtype.val h)) (fun h => hψb (congrArg Subtype.val h))
    obtain ⟨h, hh⟩ := hψsurj σ σ.2
    have hσ' : ψ (h⁻¹ * k * h) = ψ b := by
      have := congrArg Subtype.val hσ
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [map_mul, map_mul, map_inv, hh]
      exact this
    exact ⟨h, Or.inr (jq_eq_of_psi_eq hKM hOKM hψker hσ')⟩

theorem exists_conj_of_involution_mem_sup_of_models
    {K L M : Subgroup X} (hKM : K ≤ M) (hLM : L ≤ M) (hcomm : ⁅K, L⁆ ≤ oddIn K ⊓ oddIn L)
    (hOKM : oddIn K ≤ oddIn M) (hOLM : oddIn L ≤ oddIn M)
    {ψK : ↥K →* Equiv.Perm (Fin 42)} (hKS : ∀ y, ψK y ∈ PSL3Four.S)
    (hKsurj : ∀ s ∈ PSL3Four.S, ∃ y, ψK y = s) (hKker : ∀ y, ψK y = 1 ↔ y ∈ pPrimeCore 2 ↥K)
    {ψL : ↥L →* Equiv.Perm (Fin 42)} (hLS : ∀ y, ψL y ∈ PSL3Four.S)
    (hLsurj : ∀ s ∈ PSL3Four.S, ∃ y, ψL y = s) (hLker : ∀ y, ψL y = 1 ↔ y ∈ pPrimeCore 2 ↥L)
    {a b : X} (haL : a ∈ L) (hbK : b ∈ K) (haa : a * a = 1) (ha1 : a ≠ 1) (hbb : b * b = 1)
    (hb1 : b ≠ 1) {y : X} (hy : y ∈ K ⊔ L ⊔ oddIn M) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g ∈ M, g⁻¹ * y * g = a ∨ g⁻¹ * y * g = b ∨ (g⁻¹ * y * g)⁻¹ * a * b ∈ oddIn M := by
  have hOM : oddIn M ≤ M := map_subtype_le _
  have hKL : ∀ (k : ↥K) (l : ↥L),
      Commute (L34Facts.jq M (inclusion hKM k)) (L34Facts.jq M (inclusion hLM l)) := by
    intro k l
    have h1 : ((⁅inclusion hKM k, inclusion hLM l⁆ : ↥M) : X) ∈ oddIn M :=
      hOKM (mem_inf.mp (hcomm (commutator_mem_commutator k.2 l.2))).1
    have h2 : L34Facts.jq M ⁅inclusion hKM k, inclusion hLM l⁆ = 1 :=
      (L34Facts.mem_oddIn_iff (⁅inclusion hKM k, inclusion hLM l⁆ : ↥M).2).mp h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  let φ : ↥K × ↥L →* L34Facts.Jhat M :=
    ((L34Facts.jq M).comp (inclusion hKM)).noncommCoprod ((L34Facts.jq M).comp (inclusion hLM))
      hKL
  have hφ : ∀ p : ↥K × ↥L,
      φ p = L34Facts.jq M (inclusion hKM p.1) * L34Facts.jq M (inclusion hLM p.2) :=
    fun p => MonoidHom.noncommCoprod_apply _ _ _ p
  have hKnL : K ≤ normalizer (L : Set X) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans (inf_le_right.trans (map_subtype_le _)))
  have hKLO : K ⊔ L ≤ normalizer ((oddIn M : Subgroup X) : Set X) :=
    (sup_le hKM hLM).trans (self_le_normalizer_oddIn M)
  obtain ⟨k, l, o, hkl⟩ : ∃ (k : ↥K) (l : ↥L) (o : ↥(oddIn M)), (k : X) * l * o = y := by
    have hy' : y ∈ ((K ⊔ L : Subgroup X) : Set X) * ((oddIn M : Subgroup X) : Set X) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hKLO]
      exact hy
    obtain ⟨x, hx, o, ho, rfl⟩ := Set.mem_mul.mp hy'
    have hx' : x ∈ (K : Set X) * (L : Set X) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hKnL]
      exact hx
    obtain ⟨k, hk, l, hl, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨⟨k, hk⟩, ⟨l, hl⟩, ⟨o, ho⟩, rfl⟩
  have hyM : y ∈ M := (sup_le (sup_le hKM hLM) hOM) hy
  have hybar : L34Facts.jq M ⟨y, hyM⟩ = φ (k, l) := by
    have e1 : (⟨y, hyM⟩ : ↥M) = inclusion hKM k * inclusion hLM l * ⟨(o : X), hOM o.2⟩ :=
      Subtype.ext hkl.symm
    have ho1 : L34Facts.jq M ⟨(o : X), hOM o.2⟩ = 1 := (L34Facts.mem_oddIn_iff (hOM o.2)).mp o.2
    rw [e1, map_mul, map_mul, ho1, mul_one, hφ]
  have hsq : L34Facts.jq M (inclusion hKM (k * k)) * L34Facts.jq M (inclusion hLM (l * l)) =
      1 := by
    have h1 : L34Facts.jq M ⟨y, hyM⟩ * L34Facts.jq M ⟨y, hyM⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hyM⟩ : ↥M) * ⟨y, hyM⟩ = 1 := Subtype.ext hy2
      rw [this, map_one]
    rw [hybar, ← map_mul φ, Prod.mk_mul_mk, hφ] at h1
    exact h1
  have hk2 : ψK (k * k) = 1 := by
    refine psi_eq_one_of_commute hKM hKS hKsurj hKker fun x => ?_
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact (hKL x _).inv_right
  have hl2 : ψL (l * l) = 1 := by
    refine psi_eq_one_of_commute hLM hLS hLsurj hLker fun x => ?_
    rw [eq_inv_of_mul_eq_one_right hsq]
    exact (hKL _ x).symm.inv_right
  have ha'2 : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext haa
  have ha'1 : (⟨a, haL⟩ : ↥L) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb'2 : (⟨b, hbK⟩ : ↥K) * ⟨b, hbK⟩ = 1 := Subtype.ext hbb
  have hb'1 : (⟨b, hbK⟩ : ↥K) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨h₁, hh₁⟩ := exists_conj_jq_eq hKM hOKM hKS hKsurj hKker hb'2 hb'1 hk2
  obtain ⟨h₂, hh₂⟩ := exists_conj_jq_eq hLM hOLM hLS hLsurj hLker ha'2 ha'1 hl2
  have hg₀M : (h₁ : X) * h₂ ∈ M := mul_mem (hKM h₁.2) (hLM h₂.2)
  have hy'M : ((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂) ∈ M :=
    mul_mem (mul_mem (inv_mem hg₀M) hyM) hg₀M
  have hconj : L34Facts.jq M ⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩ =
      L34Facts.jq M (inclusion hKM (h₁⁻¹ * k * h₁)) *
        L34Facts.jq M (inclusion hLM (h₂⁻¹ * l * h₂)) := by
    have e1 : (⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩ : ↥M) =
        (inclusion hKM h₁ * inclusion hLM h₂)⁻¹ * ⟨y, hyM⟩ *
          (inclusion hKM h₁ * inclusion hLM h₂) := rfl
    have e2 : L34Facts.jq M (inclusion hKM h₁ * inclusion hLM h₂) = φ (h₁, h₂) := by
      rw [map_mul, hφ]
    rw [e1, map_mul, map_mul, map_inv, e2, hybar, ← map_inv φ, ← map_mul φ, ← map_mul φ, hφ]
    rfl
  have hy'2 : (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂)) * (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂)) = 1 := by
    rw [show ((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂) * (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂)) =
      ((h₁ : X) * h₂)⁻¹ * (y * y) * (h₁ * h₂) by group, hy2]
    group
  have hjq : ∀ z : ↥M, L34Facts.jq M z = 1 ↔ z ∈ pPrimeCore 2 ↥M :=
    fun z => QuotientGroup.eq_one_iff z
  have hfin : ∀ (c : X) (hc : c ∈ M), c * c = 1 →
      L34Facts.jq M ⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩ = L34Facts.jq M ⟨c, hc⟩ →
        ∃ g ∈ M, g⁻¹ * y * g = c := by
    intro c hc hc2 he
    obtain ⟨d, -, hd⟩ := exists_conj_of_psi_eq hjq
      (x := ⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩) (y := ⟨c, hc⟩)
      (Subtype.ext hy'2) (Subtype.ext hc2) he
    refine ⟨(h₁ : X) * h₂ * d, mul_mem hg₀M d.2, ?_⟩
    have h1 : (d : X)⁻¹ * (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂)) * d = c :=
      congrArg Subtype.val hd
    rw [← h1]
    group
  rcases hh₁ with h₁1 | h₁b <;> rcases hh₂ with h₂1 | h₂a
  ·
    exfalso
    have h1 : L34Facts.jq M ⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩ = 1 := by
      rw [hconj, h₁1, h₂1, mul_one]
    have h2 := eq_one_of_mem_pPrimeCore_of_two_pow ((hjq _).mp h1) (n := 1)
      (by rw [pow_one, pow_two]; exact Subtype.ext hy'2)
    have h3 : ((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂) = 1 := congrArg Subtype.val h2
    apply hy1
    calc y = ((h₁ : X) * h₂) * (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂)) * ((h₁ : X) * h₂)⁻¹ := by
          group
      _ = 1 := by rw [h3]; group
  ·
    obtain ⟨g, hg, hgy⟩ := hfin a (hLM haL) haa (by rw [hconj, h₁1, h₂a, one_mul]; rfl)
    exact ⟨g, hg, Or.inl hgy⟩
  ·
    obtain ⟨g, hg, hgy⟩ := hfin b (hKM hbK) hbb (by rw [hconj, h₁b, h₂1, mul_one]; rfl)
    exact ⟨g, hg, Or.inr (Or.inl hgy)⟩
  ·
    refine ⟨(h₁ : X) * h₂, hg₀M, Or.inr (Or.inr ?_)⟩
    have hm : (((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂))⁻¹ * a * b ∈ M :=
      mul_mem (mul_mem (inv_mem hy'M) (hLM haL)) (hKM hbK)
    rw [L34Facts.mem_oddIn_iff hm]
    have e1 : (⟨(((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂))⁻¹ * a * b, hm⟩ : ↥M) =
        (⟨((h₁ : X) * h₂)⁻¹ * y * (h₁ * h₂), hy'M⟩ : ↥M)⁻¹ * inclusion hLM ⟨a, haL⟩ *
          inclusion hKM ⟨b, hbK⟩ := rfl
    rw [e1, map_mul, map_mul, map_inv, hconj, h₁b, h₂a, (hKL ⟨b, hbK⟩ ⟨a, haL⟩).eq]
    group

theorem exists_conj_of_involution_mem_sup {a : X}
    {J W K : Subgroup X} (hs : SingleComponentSetting X a J W K)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hZ : zStarIn J = oddIn J) {u : X}
    (hu : u ∈ normalizer (W : Set X)) (hKu : conjugate K u ≠ K) (haKu : a ∈ conjugate K u)
    (hr : ∀ m ∈ normalizer (W : Set X), conjugate K m = K ∨ conjugate K m = conjugate K u)
    {y : X} (hy : y ∈ K ⊔ conjugate K u ⊔ oddIn (normalizer (W : Set X))) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) :
    ∃ g ∈ normalizer (W : Set X), g⁻¹ * y * g = a ∨ g⁻¹ * y * g = u⁻¹ * a * u ∨
      (g⁻¹ * y * g)⁻¹ * a * (u⁻¹ * a * u) ∈ oddIn (normalizer (W : Set X)) := by
  have hgs := hs.toGSMaximalSetting
  have hKM : K ≤ normalizer (W : Set X) := hs.le_normalizer
  have hKc := hs.isPComponent_K
  have hLM : conjugate K u ≤ normalizer (W : Set X) := conjugate_le_of_mem hKM hu
  have hLc : IsPComponent 2 ((conjugate K u).subgroupOf (normalizer (W : Set X))) :=
    isPComponent_conjugate_subgroupOf hu hKc
  obtain ⟨ψK, hKS, hKsurj, hKker⟩ := exists_hom_model_self hs hL34 hZ
  obtain ⟨ψL, hLS, hLsurj, hLker⟩ := exists_hom_model hs hL34 hZ u
  have haa : a * a = 1 := by rw [← pow_two, ← hgs.orderOf_eq, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by
    have h2 := hgs.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hKuu : conjugate K (u * u) = K := by
    rcases hr (u * u) (mul_mem hu hu) with h | h
    · exact h
    · refine absurd ?_ hKu
      ext x
      have h1 := SetLike.ext_iff.mp h (u⁻¹ * x * u)
      rw [mem_conjugate_iff, mem_conjugate_iff,
        show u * u * (u⁻¹ * x * u) * (u * u)⁻¹ = u * x * u⁻¹ by group,
        show u * (u⁻¹ * x * u) * u⁻¹ = x by group] at h1
      rw [mem_conjugate_iff]
      exact h1
  have hbK : u⁻¹ * a * u ∈ K := by
    rw [← hKuu, mem_conjugate_iff,
      show u * u * (u⁻¹ * a * u) * (u * u)⁻¹ = u * a * u⁻¹ by group]
    exact mem_conjugate_iff.mp haKu
  have hbb : u⁻¹ * a * u * (u⁻¹ * a * u) = 1 := by
    rw [show u⁻¹ * a * u * (u⁻¹ * a * u) = u⁻¹ * (a * a) * u by group, haa]
    group
  have hb1 : u⁻¹ * a * u ≠ 1 := fun h => ha1 (by
    calc a = u * (u⁻¹ * a * u) * u⁻¹ := by group
      _ = 1 := by rw [h]; group)
  exact exists_conj_of_involution_mem_sup_of_models hKM hLM
    (GrS5.commutator_le_inf_oddIn hKM hLM hKc hLc (Ne.symm hKu))
    (GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc)
    (GSLit.map_pPrimeCore_le_of_isPComponent hLM hLc) hKS hKsurj hKker hLS hLsurj hLker
    haKu hbK haa ha1 hbb hb1 hy hy2 hy1

end CFSG.ComponentClassification.GrSLit.FW
