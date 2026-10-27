module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bPerfectAction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bL34Tools

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem exists_pow_odd_orderOf_map_eq {G Q : Type*} [Group G] [Finite G] [Group Q]
    (π : G →* Q) (g : G) (hg : Odd (orderOf (π g))) :
    ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ π (g ^ k) = π g := by
  obtain ⟨v, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set d := orderOf (π g) with hd
  have hcop : Nat.Coprime (2 ^ v) d := Nat.Coprime.pow_left v (Nat.coprime_two_left.mpr hg)
  have hgm : g ^ (2 ^ v * m) = 1 := by rw [← hn, pow_orderOf_eq_one]
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · have hd0 : d ≠ 0 := fun h0 => by
      rw [h0] at hg
      obtain ⟨r, hr⟩ := hg
      omega
    have hd1 : d = 1 := by omega
    refine ⟨orderOf g, ?_, ?_⟩
    · rw [pow_orderOf_eq_one, orderOf_one]
      exact odd_one
    · rw [pow_orderOf_eq_one, map_one]
      exact (orderOf_eq_one_iff.mp hd1).symm
  · obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hd2
    refine ⟨2 ^ v * w, ?_, ?_⟩
    · have hdvd : orderOf (g ^ (2 ^ v * w)) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, show 2 ^ v * w * m = 2 ^ v * m * w by ring, pow_mul, hgm, one_pow]
      exact hm.of_dvd_nat hdvd
    · rw [map_pow, ← pow_mod_orderOf, ← hd, hw, pow_one]

theorem exists_twoSubgroup_lift {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    {A : Subgroup (G ⧸ pPrimeCore 2 G)} (hA : IsPGroup 2 A)
    (hAM : A ≤ M.map (QuotientGroup.mk' (pPrimeCore 2 G))) :
    ∃ R : Subgroup G, R ≤ M ∧ R.map (QuotientGroup.mk' (pPrimeCore 2 G)) = A ∧
      ∀ u ∈ R, ∀ v ∈ R, QuotientGroup.mk' (pPrimeCore 2 G) u =
        QuotientGroup.mk' (pPrimeCore 2 G) v → u = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 G) with hπ
  set M' : Subgroup G := M ⊓ A.comap π with hM'
  set f : M' →* G ⧸ pPrimeCore 2 G := π.comp M'.subtype with hf
  have hrange : f.range = A := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (mem_inf.mp m.2).2
    · intro y hy
      obtain ⟨m, hm, rfl⟩ := mem_map.mp (hAM hy)
      exact ⟨⟨m, mem_inf.mpr ⟨hm, hy⟩⟩, rfl⟩
  have hkerodd : Nat.Coprime 2 (Nat.card f.ker) := by
    set g₀ : f.ker →* G := M'.subtype.comp f.ker.subtype with hg₀
    have hg₀inj : Function.Injective g₀ := M'.subtype_injective.comp f.ker.subtype_injective
    have hle : g₀.range ≤ pPrimeCore 2 G := by
      rintro _ ⟨k, rfl⟩
      have hk : QuotientGroup.mk' (pPrimeCore 2 G) ((k : M') : G) = 1 := k.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    have h1 : Nat.card f.ker = Nat.card g₀.range :=
      Nat.card_congr (MonoidHom.ofInjective hg₀inj).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (CFSG.pPrimeCore_coprime_card (p := 2))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcardM : Nat.card M' = Nat.card A * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 M'))
  have hRcard : Nat.card R = Nat.card A := by
    rw [Sylow.card_eq_multiplicity, hcardM, hk]
    have hk0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
    have hodd : ¬ 2 ∣ Nat.card f.ker := fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right h2 hkerodd) (by norm_num)
    rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  have hRker : (R : Subgroup M') ⊓ f.ker = ⊥ := by
    apply eq_bot_of_isPGroup_two_of_coprime (R.isPGroup'.to_le inf_le_left)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hkerodd
  have hinj : ∀ u ∈ (R : Subgroup M'), ∀ v ∈ (R : Subgroup M'), f u = f v → u = v := by
    intro u hu v hv huv
    have : u⁻¹ * v ∈ (R : Subgroup M') ⊓ f.ker := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hu) hv, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [hRker, mem_bot] at this
    calc u = u * (u⁻¹ * v) := by rw [this, mul_one]
      _ = v := by group
  have hinj' : Function.Injective (f.comp (R : Subgroup M').subtype) := fun u v huv =>
    Subtype.ext (hinj u u.2 v v.2 huv)
  have hfR : (R : Subgroup M').map f = A := by
    have hmap : (R : Subgroup M').map f = (f.comp (R : Subgroup M').subtype).range := by
      rw [MonoidHom.range_comp, range_subtype]
    have hcard : Nat.card ((R : Subgroup M').map f) = Nat.card A := by
      rw [hmap, ← hRcard]
      exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm
    have hle : (R : Subgroup M').map f ≤ A := by
      rw [← hrange]
      exact map_le_range f _
    exact eq_of_le_of_card_ge hle hcard.ge
  refine ⟨(R : Subgroup M').map M'.subtype, (map_subtype_le _).trans inf_le_left, ?_, ?_⟩
  · rw [Subgroup.map_map]
    exact hfR
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    exact congrArg Subtype.val (hinj u hu v hv huv)

section Action

variable {G : Type} [Group G]

theorem oddBarConj_eq_one_of_mem_coreActionKernel {L : Subgroup G}
    {g : ↥(normalizer (L : Set G))} (hg : (g : G) ∈ coreActionKernel L) : oddBarConj L g = 1 := by
  obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hg
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have hj : (g : G) * y * (g : G)⁻¹ ∈ L := (mem_normalizer_iff.mp g.2 y).mp y.2
  obtain ⟨o, ho, hoe⟩ := mem_map.mp (hc _ hj)
  convert ho using 1
  apply Subtype.ext
  rw [subtype_apply] at hoe
  rw [hoe]
  simp only [coe_mul, coe_inv]
  group

theorem oddBarConj_eq_conj {L : Subgroup G} (k : L) (hk : (k : G) ∈ normalizer (L : Set G)) :
    oddBarConj L ⟨k, hk⟩ = MulAut.conj (k : L ⧸ pPrimeCore 2 L) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem mem_coreActionKernel_of_odd {J : Subgroup G} {z x : G} (hzJ : z ∈ J)
    (hxN : x ∈ normalizer (J : Set G)) (hxz : x * z = z * x)
    (hstab : IsPGroup 2 ↥(MulAction.stabilizer (MulAut (J ⧸ pPrimeCore 2 J))
      ((⟨z, hzJ⟩ : J) : J ⧸ pPrimeCore 2 J)))
    (hodd : Odd (orderOf x)) : x ∈ coreActionKernel J := by
  set φ := oddBarConj J ⟨x, hxN⟩ with hφ
  have hφs : φ ∈ MulAction.stabilizer (MulAut (J ⧸ pPrimeCore 2 J))
      ((⟨z, hzJ⟩ : J) : J ⧸ pPrimeCore 2 J) := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hφ, oddBarConj_apply_mk]
    congr 1
    apply Subtype.ext
    show x * z * x⁻¹ = z
    rw [hxz, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := hstab ⟨φ, hφs⟩
  have h1 : orderOf φ ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    exact congrArg Subtype.val hn
  have h2 : orderOf φ ∣ orderOf x := by
    have := orderOf_map_dvd (oddBarConj J) (⟨x, hxN⟩ : ↥(normalizer (J : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf φ = 1 := by
    have hcop : Nat.Coprime (2 ^ n) (orderOf x) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact mem_coreActionKernel_of_oddBarConj_eq_one (orderOf_eq_one_iff.mp h3)

theorem le_coreActionKernel_of_perfect {J X : Subgroup G} {z : G} (hzJ : z ∈ J)
    (hXN : X ≤ normalizer (J : Set G)) (hXz : ∀ x ∈ X, x * z = z * x)
    (hstab : Group.IsSolvable ↥(MulAction.stabilizer (MulAut (J ⧸ pPrimeCore 2 J))
      ((⟨z, hzJ⟩ : J) : J ⧸ pPrimeCore 2 J)))
    (hX : ⁅X, X⁆ = X) : X ≤ coreActionKernel J := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  set ρ := (oddBarConj J).comp (inclusion hXN) with hρ
  have hle : ρ.range ≤ MulAction.stabilizer (MulAut (J ⧸ pPrimeCore 2 J))
      ((⟨z, hzJ⟩ : J) : J ⧸ pPrimeCore 2 J) := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hρ, MonoidHom.comp_apply]
    show oddBarConj J ⟨y, hXN hy⟩ _ = _
    rw [oddBarConj_apply_mk]
    congr 1
    apply Subtype.ext
    show y * z * y⁻¹ = z
    rw [hXz y hy, mul_inv_cancel_right]
  have hsol : Group.IsSolvable ρ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  intro x hx
  exact mem_coreActionKernel_of_perfect_of_solvable (inclusion hXN) hsol ⟨x, hx⟩

end Action

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem exists_conjugate_le_P (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) {E : Subgroup H}
    (hEC : E ≤ centralizer ({h.a} : Set H)) (hEK : E ≤ coreActionKernel h.J)
    (hE : IsPGroup 2 E) : ∃ m : H, conjugate E m ≤ h.P := by
  obtain ⟨-, hSyl⟩ := h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨m, hm, hmS⟩ := exists_conjugate_le_of_sylow hSyl hEC hE
  have hmN := h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc hm
  refine ⟨m, fun y hy => mem_inf.mpr ⟨hmS hy, ?_⟩⟩
  have hJm : conjugate h.J m = h.J := by
    unfold conjugate
    exact (mem_normalizer_iff_map_conj_eq.mp (inv_mem hmN))
  rw [← hJm, ← conjugate_coreActionKernel, mem_conjugate_iff]
  exact hEK (mem_conjugate_iff.mp hy)

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem isCyclic_of_le_P (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) {A : Subgroup H} (hAP : A ≤ h.P)
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hA8 : 8 ≤ Nat.card A) : IsCyclic A := by
  obtain ⟨C, hCP, hCc, hPC⟩ := h.exists_cyclic_index_two hB7 hST hT
  obtain ⟨b, hBb, hb, hT4, -, hTC⟩ := h.index_two_structure hB7 hT
  have hbP : b ∈ h.P := h.toHyp52.B_le_P (hBb ▸ mem_zpowers b)
  have := hCc
  by_cases hAC : A ≤ C
  · exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hAC).surjective
  exfalso
  obtain ⟨u, huA, huC⟩ := Set.not_subset.mp hAC
  have hCP0 : C.relIndex h.P ≠ 0 := by
    rw [relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hrel : C.relIndex A ≤ 2 := by
    refine (relIndex_le_of_le_right hAP hCP0).trans ?_
    have hc := Subgroup.card_mul_index (C.subgroupOf h.P)
    have hcC : Nat.card (C.subgroupOf h.P) = Nat.card C := by
      rw [← Subgroup.card_map_of_injective h.P.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left hCP]
    rw [hcC] at hc
    have hC0 : 0 < Nat.card C := Nat.card_pos
    rw [relIndex]
    by_contra hlt
    push Not at hlt
    have : 3 * Nat.card C ≤ Nat.card h.P := by
      calc 3 * Nat.card C ≤ (C.subgroupOf h.P).index * Nat.card C := Nat.mul_le_mul_right _ hlt
        _ = Nat.card h.P := by rw [← hc, mul_comm]
    omega
  have hAC4 : 4 ≤ Nat.card ↥(A ⊓ C) := by
    have hc := Subgroup.card_mul_index (C.subgroupOf A)
    have hc' : Nat.card (C.subgroupOf A) = Nat.card ↥(A ⊓ C) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective, subgroupOf_map_subtype, inf_comm]
    rw [hc'] at hc
    have : Nat.card A ≤ Nat.card ↥(A ⊓ C) * 2 := by
      rw [← hc]
      exact Nat.mul_le_mul_left _ hrel
    omega
  have : IsCyclic ↥(A ⊓ C) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ C ≤ C)).surjective
  obtain ⟨y, hgen⟩ := IsCyclic.exists_generator (α := ↥(A ⊓ C))
  have hyord : 4 ≤ orderOf (y : H) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact hAC4
  obtain ⟨hyA, hyC⟩ := mem_inf.mp y.2
  have hsup : C ⊔ zpowers u = h.P := by
    have hle : C ⊔ zpowers u ≤ h.P := sup_le hCP (zpowers_le.mpr (hAP huA))
    apply eq_of_le_of_card_ge hle
    have hlt : C < C ⊔ zpowers u :=
      lt_of_le_of_ne le_sup_left fun he => huC (he ▸ mem_sup_right (mem_zpowers u))
    have hdvd : Nat.card C ∣ Nat.card ↥(C ⊔ zpowers u) := Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card C ≠ Nat.card ↥(C ⊔ zpowers u) := fun he =>
      (ne_of_lt hlt) (eq_of_le_of_card_ge le_sup_left he.ge)
    obtain ⟨r, hr⟩ := hdvd
    have hC0 : 0 < Nat.card C := Nat.card_pos
    have hr2 : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h2 | h2
      · interval_cases r
        · have : Nat.card ↥(C ⊔ zpowers u) = 0 := by rw [hr, mul_zero]
          exact absurd this Nat.card_pos.ne'
        · exact absurd (by rw [hr, mul_one]) hne
      · exact h2
    calc Nat.card h.P ≤ 2 * Nat.card C := hPC
      _ ≤ r * Nat.card C := Nat.mul_le_mul_right _ hr2
      _ = Nat.card ↥(C ⊔ zpowers u) := by rw [hr, mul_comm]
  have hCcomm : ∀ w ∈ C, w * (y : H) = (y : H) * w := by
    intro w hw
    obtain ⟨⟨g₀, hg₀⟩, hgen₀⟩ := IsCyclic.exists_generator (α := C)
    obtain ⟨i, hi⟩ := hgen₀ ⟨w, hw⟩
    obtain ⟨j, hj⟩ := hgen₀ ⟨(y : H), hyC⟩
    have hw' : w = g₀ ^ i := by
      have := congrArg Subtype.val hi
      simpa using this.symm
    have hy' : (y : H) = g₀ ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [hw', hy', ← zpow_add, ← zpow_add, add_comm]
  have hycent : h.P ≤ centralizer ({(y : H)} : Set H) := by
    rw [← hsup]
    refine sup_le (fun w hw => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact hCcomm w hw
    · rw [mem_centralizer_singleton_iff]
      exact hAc u huA _ hyA
  have hyT : zpowers (y : H) ≤ h.T := by
    rw [zpowers_le, hTC]
    refine mem_inf.mpr ⟨hCP hyC, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hycent hbP)).symm
  have hyTeq : zpowers (y : H) = h.T := by
    apply eq_of_le_of_card_ge hyT
    rw [hT4, Nat.card_zpowers]
    exact hyord
  have hbT : b ∈ h.T := by
    rw [hTC]
    exact mem_inf.mpr ⟨hbP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hbcent : h.P ≤ centralizer ({b} : Set H) := by
    intro w hw
    rw [← hyTeq] at hbT
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hbT
    rw [mem_centralizer_singleton_iff]
    exact ((Commute.zpow_left (show Commute (y : H) w from
      (mem_centralizer_singleton_iff.mp (hycent hw)).symm) k).eq).symm
  have hPT : h.P = h.T := by
    rw [hTC]
    exact (inf_of_le_left hbcent).symm
  have hA4 : Nat.card A ≤ 4 := by
    rw [← hT4, ← hPT]
    exact Subgroup.card_le_of_le hAP
  omega

theorem eq_of_involutions (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) {F : Subgroup H}
    (hFC : F ≤ centralizer ({h.a} : Set H)) (hFK : F ≤ coreActionKernel h.J)
    (hF2 : IsPGroup 2 F) (hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u) (hF8 : 8 ≤ Nat.card F)
    {u v : H} (hu : u ∈ F) (hv : v ∈ F) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) :
    u = v := by
  classical
  obtain ⟨m, hm⟩ := h.toHyp52.exists_conjugate_le_P hB1 hB6 hCF23 hCF24 hCFc hFC hFK hF2
  set F' := conjugate F m with hF'
  have hF'c : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    rw [mem_conjugate_iff] at hx hy
    have := hFc _ hx _ hy
    calc x * y = m⁻¹ * ((m * x * m⁻¹) * (m * y * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * y * m⁻¹) * (m * x * m⁻¹)) * m := by rw [this]
      _ = y * x := by group
  have hcard : Nat.card F' = Nat.card F := by
    rw [hF', conjugate]
    exact card_map_of_injective (MulAut.conj m⁻¹).injective
  have := h.isCyclic_of_le_P hB7 hST hT hm hF'c (hcard ▸ hF8)
  have hmem : ∀ {w : H}, w ∈ F → m⁻¹ * w * m ∈ F' := fun {w} hw => by
    rw [hF', mem_conjugate_iff]
    convert hw using 1
    group
  have hsq : ∀ {w : H}, orderOf w = 2 → (m⁻¹ * w * m) ^ 2 = 1 := fun {w} hw => by
    have h1 : (m⁻¹ * w * m) ^ 2 = m⁻¹ * w ^ 2 * m := by rw [pow_two, pow_two]; group
    rw [h1, ← hw, pow_orderOf_eq_one]
    group
  have hne1 : ∀ {w : H}, orderOf w = 2 → m⁻¹ * w * m ≠ 1 := fun {w} hw he => by
    have : w = 1 := by
      calc w = m * (m⁻¹ * w * m) * m⁻¹ := by group
        _ = 1 := by rw [he]; group
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)
  set u' : F' := ⟨m⁻¹ * u * m, hmem hu⟩ with hu'
  set v' : F' := ⟨m⁻¹ * v * m, hmem hv⟩ with hv'
  by_contra huv
  have : Fintype F' := Fintype.ofFinite F'
  have hle := IsCyclic.card_pow_eq_one_le (α := F') (n := 2) (by norm_num)
  have h1u : (1 : F') ≠ u' := fun he => hne1 hu2 (congrArg Subtype.val he).symm
  have h1v : (1 : F') ≠ v' := fun he => hne1 hv2 (congrArg Subtype.val he).symm
  have huv' : u' ≠ v' := fun he => by
    apply huv
    have h1 : m⁻¹ * u * m = m⁻¹ * v * m := congrArg Subtype.val he
    calc u = m * (m⁻¹ * u * m) * m⁻¹ := by group
      _ = m * (m⁻¹ * v * m) * m⁻¹ := by rw [h1]
      _ = v := by group
  have h3 : ({1, u', v'} : Finset F') ⊆ Finset.univ.filter (fun x : F' => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hsq hu2)
    · exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hsq hv2)
  have hc3 : ({1, u', v'} : Finset F').card = 3 :=
    Finset.card_eq_three.mpr ⟨1, u', v', h1u, h1v, huv', rfl⟩
  have := Finset.card_le_card h3
  omega

end Hyp59

end CFSG.ComponentClassification.GSThmB
