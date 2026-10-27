module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9E
public import CFSG.LocalAnalysis.ComponentClassification.Sol78InputsGen
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem not_two_pow_nine_dvd_card_of_le [Finite X] {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) (hm : m ≤ 11)
    {H : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {K : Subgroup X} (hKH : K ≤ H) : ¬ 2 ^ 9 ∣ Nat.card K := by
  classical
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥K →* Perm (Fin m) := ρ.comp (inclusion (hKH.trans hHN)) with hfdef
  have hodd : ¬ 2 ∣ Nat.card f.ker := by
    intro h2
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 h2
    have hgK : ((g : ↥K) : X) ∈ UnbalancedLayer.coreActionKernel M :=
      hρ.mem_coreActionKernel (hHN (hKH (g : ↥K).2)) g.2
    have h1 := hker _ (hKH (g : ↥K).2) hgK
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg] at h1
    exact absurd h1 (by decide)
  have hcard : Nat.card ↥K = Nat.card f.range * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hcop : Nat.Coprime (2 ^ 9) (Nat.card f.ker) :=
    Nat.Coprime.pow_left 9 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h1 : 2 ^ 9 ∣ Nat.card f.range := by
    rw [hcard] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have h2 : Nat.card f.range ∣ Nat.factorial 11 := by
    have h3 := card_subgroup_dvd_card f.range
    rw [Nat.card_perm, Nat.card_fin] at h3
    exact h3.trans (Nat.factorial_dvd_factorial hm)
  have h4 := h1.trans h2
  revert h4
  decide

theorem mem_of_map_conj_le_sup_odd [Finite X] {H F O : Subgroup X}
    (hFH : normalizer (F : Set X) ≤ H) (hFH' : F ≤ H) (hOH : O ≤ H) (hF2 : IsPGroup 2 F)
    (hFO : F ≤ normalizer (O : Set X)) (hO : Odd (Nat.card O)) {x : X}
    (hx : F.map (MulAut.conj x).toMonoidHom ≤ F ⊔ O) : x ∈ H := by
  obtain ⟨c, hc, hcF⟩ := exists_conj_of_le_sup_odd' hFO hF2 hO hx
    (card_map_of_injective (MulAut.conj x).injective)
  have hcH : c ∈ H := (sup_le hFH' hOH) hc
  have hcx : c * x ∈ normalizer (F : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc F.map (MulAut.conj (c * x)).toMonoidHom =
        (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
      _ = F := hcF
  have h1 := mul_mem (inv_mem hcH) (hFH hcx)
  rwa [inv_mul_cancel_left] at h1

theorem exists_coreQuot_equiv_of_surjective {A B : Type*} [Group A] [Finite A] [Group B]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    {k : ℕ} (hk : 5 ≤ k) (χ : A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin k)) :
    ∃ e : B ⧸ pPrimeCore 2 B ≃* alternatingGroup (Fin k), ∀ a : A,
      e ((f a : B) : B ⧸ pPrimeCore 2 B) = χ (a : A ⧸ pPrimeCore 2 A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : A →* alternatingGroup (Fin k) :=
    χ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A)) with hφdef
  have hφ : ∀ a, φ a = 1 ↔ a ∈ pPrimeCore 2 A := fun a => by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerO : f.ker ≤ pPrimeCore 2 A :=
    le_sSup ⟨f.normal_ker, Nat.coprime_two_left.mpr hker⟩
  have hle : f.ker ≤ φ.ker := fun a ha => (hφ a).mpr (hkerO ha)
  set ψ : B →* alternatingGroup (Fin k) :=
    (QuotientGroup.lift f.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom with hψdef
  have hψf : ∀ a, ψ (f a) = φ a := by
    intro a
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) =
        (a : A ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hφs : Function.Surjective φ := χ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := hφs y
    exact ⟨f a, hψf a⟩
  have hψker : Odd (Nat.card ψ.ker) := by
    have h1 : ψ.ker ≤ (pPrimeCore 2 A).map f := by
      intro b hb
      obtain ⟨a, rfl⟩ := hf b
      have h2 : φ a = 1 := by
        rw [← hψf a]
        exact hb
      exact ⟨a, (hφ a).mp h2, rfl⟩
    have h3 : Nat.card ψ.ker ∣ Nat.card (pPrimeCore 2 A) :=
      (card_dvd_of_le h1).trans (card_map_dvd _ _)
    exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have heven : Even (Nat.card (alternatingGroup (Fin k))) :=
    even_card_alternatingGroup (by rw [Fintype.card_fin]; omega)
  have hO : pPrimeCore 2 B = ψ.ker := pPrimeCore_eq_ker ψ hψs hψker heven
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs), fun a => ?_⟩
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  change ψ (f a) = _
  rw [hψf]
  rfl

@[expose] noncomputable def coreQuotAut (N : Subgroup X) (g : ↥(normalizer (N : Set X))) :
    MulAut (↥N ⧸ pPrimeCore 2 ↥N) :=
  QuotientGroup.congr _ _ (N.normalizerMonoidHom g) (by
    have h := characteristic_iff_map_eq.mp (inferInstance : (pPrimeCore 2 ↥N).Characteristic)
      (N.normalizerMonoidHom g)
    exact h)

theorem coreQuotAut_mk (N : Subgroup X) (g : ↥(normalizer (N : Set X))) (y : ↥N) :
    coreQuotAut N g (y : ↥N ⧸ pPrimeCore 2 ↥N) =
      ((N.normalizerMonoidHom g y : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) :=
  rfl

theorem fixed_le_map_centralizer [Finite X] {N : Subgroup X} {e₁ : X}
    (he₁N : e₁ ∈ normalizer (N : Set X)) (he₁2 : e₁ * e₁ = 1) :
    Open.signalizerFixedSubgroup (coreQuotAut N ⟨e₁, he₁N⟩) ≤
      ((centralizer ({e₁} : Set X)).subgroupOf N).map (QuotientGroup.mk' (pPrimeCore 2 ↥N)) := by
  classical
  set c : MulAut ↥N := N.normalizerMonoidHom ⟨e₁, he₁N⟩ with hcdef
  have hcapp : ∀ y : ↥N, ((c y : ↥N) : X) = e₁ * y * e₁⁻¹ := fun y => rfl
  have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
  have hcc : ∀ y, c (c y) = y := by
    intro y
    apply Subtype.ext
    rw [hcapp, hcapp, he₁inv]
    calc e₁ * (e₁ * (y : X) * e₁) * e₁ = (e₁ * e₁) * y * (e₁ * e₁) := by group
      _ = y := by rw [he₁2]; group
  intro q hq
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥N) q
  have hw : ((c w₀ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = (w₀ : ↥N ⧸ pPrimeCore 2 ↥N) := by
    have h1 : coreQuotAut N ⟨e₁, he₁N⟩ (w₀ : ↥N ⧸ pPrimeCore 2 ↥N) =
        (w₀ : ↥N ⧸ pPrimeCore 2 ↥N) := hq
    rw [coreQuotAut_mk] at h1
    exact h1
  obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq c hcc hw
  refine ⟨w, ?_, hww⟩
  rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff]
  have h1 := congrArg Subtype.val hwc
  rw [hcapp] at h1
  calc (w : X) * e₁ = e₁ * w * e₁⁻¹ * e₁ := by rw [h1]
    _ = e₁ * w := by group

theorem map_le_layerOfFixed [Finite X] {N : Subgroup X} {e₁ : X}
    (he₁N : e₁ ∈ normalizer (N : Set X)) (he₁2 : e₁ * e₁ = 1) {L₀ : Subgroup X}
    (hL₀ : L₀ ≤ N ⊓ centralizer ({e₁} : Set X))
    (hL₀pc : IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({e₁} : Set X)))) :
    (L₀.subgroupOf N).map (QuotientGroup.mk' (pPrimeCore 2 ↥N)) ≤
      Sol78.layerOfFixed (coreQuotAut N ⟨e₁, he₁N⟩) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := N ⊓ centralizer ({e₁} : Set X) with hCdef
  set s := coreQuotAut N ⟨e₁, he₁N⟩ with hsdef
  set Fs := Open.signalizerFixedSubgroup s with hFsdef
  set O := pPrimeCore 2 ↥N with hOdef
  have hCN : C ≤ N := inf_le_left
  have hfix : ∀ y : ↥C, QuotientGroup.mk' O (inclusion hCN y) ∈ Fs := by
    intro y
    change s _ = _
    rw [QuotientGroup.mk'_apply, hsdef, coreQuotAut_mk]
    congr 1
    apply Subtype.ext
    change e₁ * (y : X) * e₁⁻¹ = y
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2
    rw [← h1]
    group
  set q : ↥C →* ↥Fs := ((QuotientGroup.mk' O).comp (inclusion hCN)).codRestrict Fs hfix with hqdef
  have hqs : Function.Surjective q := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := fixed_le_map_centralizer he₁N he₁2 hz
    refine ⟨⟨w, w.2, hw⟩, ?_⟩
    rfl
  have hqk : Odd (Nat.card q.ker) := by
    let g : q.ker →* O :=
      ((inclusion hCN).comp q.ker.subtype).codRestrict O fun x => by
        have h1 : q (x : ↥C) = 1 := x.2
        have h2 : QuotientGroup.mk' O (inclusion hCN (x : ↥C)) = 1 := congrArg Subtype.val h1
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hg : Function.Injective g := fun x y h => by
      have h' : (((x : ↥C) : X)) = ((y : ↥C) : X) := congrArg (fun z : O => ((z : ↥N) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (card_dvd_of_injective g hg)
  have hL : TwoComponents.IsTwoComponent (L₀.subgroupOf C) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hL₀pc
  have hpc : IsPComponent 2 ((L₀.subgroupOf C).map q) :=
    (CatalogueBAlternating.pComponent_two_iff _).mpr (OddKernelTwoComponents.image q hqs hqk _ hL)
  have hle : (L₀.subgroupOf C).map q ≤ pLayer ↥Fs 2 := le_sSup hpc
  rintro _ ⟨y, hy, rfl⟩
  have hyC : (y : X) ∈ C := hL₀ hy
  refine ⟨q ⟨y, hyC⟩, hle ⟨⟨y, hyC⟩, hy, rfl⟩, rfl⟩

theorem surjective_of_card_coreQuot_le {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hfk : Odd (Nat.card f.ker)) (hB : commutator B = ⊤)
    (hOZ : pPrimeCore 2 B = center B) {k : ℕ}
    (χ : A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin k))
    (hcard : Nat.card (B ⧸ pPrimeCore 2 B) ≤ Nat.card (alternatingGroup (Fin k))) :
    Function.Surjective f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set μ : A →* B ⧸ pPrimeCore 2 B := (QuotientGroup.mk' (pPrimeCore 2 B)).comp f with hμdef
  have hμ : ∀ a, μ a = 1 ↔ f a ∈ pPrimeCore 2 B := fun a => by
    rw [hμdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hμodd : Odd (Nat.card μ.ker) := by
    set g : μ.ker →* pPrimeCore 2 B :=
      (f.comp μ.ker.subtype).codRestrict _ fun a => (hμ a).mp a.2 with hgdef
    have h1 : Nat.card μ.ker = Nat.card g.range * Nat.card g.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    have h2 : Odd (Nat.card g.range) := by
      have h3 : Nat.card g.range ∣ Nat.card (pPrimeCore 2 B) := card_subgroup_dvd_card _
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card)
    have h4 : Odd (Nat.card g.ker) := by
      let j : g.ker →* f.ker := (μ.ker.subtype.comp g.ker.subtype).codRestrict _ fun a => by
        have h5 : g a = 1 := a.2
        have h6 : f ((a : μ.ker) : A) = 1 := congrArg Subtype.val h5
        exact h6
      have hj : Function.Injective j := fun a b h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : A)) h))
      exact hfk.of_dvd_nat (card_dvd_of_injective j hj)
    rw [h1]
    exact h2.mul h4
  have hμO : μ.ker ≤ pPrimeCore 2 A :=
    le_sSup ⟨μ.normal_ker, Nat.coprime_two_left.mpr hμodd⟩
  have hμs : Function.Surjective μ := by
    have h1 : Nat.card A = Nat.card μ.range * Nat.card μ.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup μ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv]
    have h2 : Nat.card A = Nat.card (alternatingGroup (Fin k)) * Nat.card (pPrimeCore 2 A) := by
      rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 A), Nat.card_congr χ.toEquiv]
    have h3 : Nat.card μ.ker ≤ Nat.card (pPrimeCore 2 A) := card_le_of_le hμO
    have h4 : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card μ.range := by
      have h5 : 0 < Nat.card (pPrimeCore 2 A) := Nat.card_pos
      have h6 : Nat.card (alternatingGroup (Fin k)) * Nat.card (pPrimeCore 2 A) ≤
          Nat.card μ.range * Nat.card (pPrimeCore 2 A) := by
        rw [← h2, h1]
        exact Nat.mul_le_mul_left _ h3
      exact Nat.le_of_mul_le_mul_right h6 h5
    exact MonoidHom.range_eq_top.mp (eq_top_of_le_card _ (hcard.trans h4))
  have hsup : f.range ⊔ center B = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨a, ha⟩ := hμs (b : B ⧸ pPrimeCore 2 B)
    have hz : (f a)⁻¹ * b ∈ center B := by
      rw [← hOZ]
      have h1 : ((f a : B) : B ⧸ pPrimeCore 2 B) = (b : B ⧸ pPrimeCore 2 B) := ha
      exact QuotientGroup.eq.mp h1
    have h1 : b = f a * ((f a)⁻¹ * b) := by group
    rw [h1]
    exact mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right hz)
  have htop := eq_top_of_sup_center_of_perfect hB hsup
  exact MonoidHom.range_eq_top.mp htop

end CFSG.ComponentClassification.SolMax
