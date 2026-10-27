module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Exp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75V

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section L3

variable {S : Type} [Group S] [Finite S] {F : Subgroup S} {a : S}

theorem mem_sup_zpowers_of_sq [F.Normal] (ha2 : a * a = 1) {x : S}
    (hx : x ∈ F ⊔ Subgroup.zpowers a) : x ∈ F ∨ ∃ f ∈ F, x = f * a := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases zpow_eq_one_or_self a ha2 n with h | h
  · left
    rw [h, mul_one]
    exact hy
  · right
    exact ⟨y, hy, by rw [h]⟩

theorem centralizer_le_of_E16 [F.Normal] (hF16 : Nat.card F = 16)
    (hZ4 : Nat.card (F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4)
    (hCZ : Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) : Set S) ≤
      F ⊔ Subgroup.zpowers a)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (ha2 : a * a = 1) :
    Subgroup.centralizer (F : Set S) ≤ F := by
  intro g hg
  have hgZ : g ∈ Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) :
      Set S) := by
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro x hx
    exact hg x hx.1
  rcases mem_sup_zpowers_of_sq ha2 (hCZ hgZ) with h | ⟨f, hf, rfl⟩
  · exact h
  · exfalso
    have hac : ∀ x ∈ F, a * x = x * a := by
      intro x hx
      have h1 : x * (f * a) = (f * a) * x := Subgroup.mem_centralizer_iff.mp hg x hx
      have h2 : x * f = f * x := hFab x hx f hf
      calc a * x = f⁻¹ * (f * (a * x)) := by group
        _ = f⁻¹ * ((f * a) * x) := by group
        _ = f⁻¹ * (x * (f * a)) := by rw [h1]
        _ = f⁻¹ * (x * f) * a := by group
        _ = f⁻¹ * (f * x) * a := by rw [h2]
        _ = x * a := by group
    have heq : F ⊓ Subgroup.centralizer ({a} : Set S) = F :=
      inf_eq_left.mpr (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hac x hx).symm)
    have hfull : Nat.card (F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 16 := by
      rw [heq, hF16]
    omega


theorem pow_four_mem_of_E16 [F.Normal] (hS : IsPGroup 2 S) (hFa : IsElemAbelian 2 F)
    (hF16 : Nat.card F = 16) (hCF : Subgroup.centralizer (F : Set S) ≤ F) (g : S) :
    g ^ 4 ∈ F := by
  apply hCF
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← pow_two]; exact hFa.2 x hx
  have h := pow_four_conj_eq hS (F := F) hab hexp
    (fun y hy s => (inferInstance : F.Normal).conj_mem y hy s) hF16.le g x hx
  calc x * g ^ 4 = (g ^ 4 * x * (g ^ 4)⁻¹) * g ^ 4 := by rw [h]
    _ = g ^ 4 * x := by group

theorem card_quot_le_eight [F.Normal] (hS : IsPGroup 2 S) (hFa : IsElemAbelian 2 F)
    (hF16 : Nat.card F = 16) (hCF : Subgroup.centralizer (F : Set S) ≤ F)
    (hcyc : ∃ C : Subgroup (S ⧸ F), IsCyclic C ∧ C.index ≤ 2) : Nat.card (S ⧸ F) ≤ 8 := by
  obtain ⟨C, hCcyc, hCi⟩ := hcyc
  have h4 : ∀ x : S ⧸ F, x ^ 4 = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_four_mem_of_E16 hS hFa hF16 hCF g
  obtain ⟨γ, hγ⟩ := hCcyc.exists_generator
  have hord : orderOf γ = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hγ4 : γ ^ 4 = 1 := Subtype.ext (h4 γ)
  have hdvd : orderOf γ ∣ 4 := orderOf_dvd_of_pow_eq_one hγ4
  have hC4 : Nat.card C ≤ 4 := by
    rw [← hord]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have := Subgroup.card_mul_index C
  nlinarith

theorem card_fix_le_four_of_commute [F.Normal] (hFa : IsElemAbelian 2 F)
    (hF16 : Nat.card F = 16)
    (hZ4 : Nat.card (F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4)
    (hCZ : Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) : Set S) ≤
      F ⊔ Subgroup.zpowers a)
    (hCF : Subgroup.centralizer (F : Set S) ≤ F) (ha2 : a * a = 1) {g : S}
    (hag : a * g * a⁻¹ * g⁻¹ ∈ F) (hgF : g ∉ F ⊔ Subgroup.zpowers a) :
    Nat.card (F ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ≤ 4 := by
  by_contra hbig
  have hbig := not_le.mp hbig
  have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFexp : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← pow_two]; exact hFa.2 x hx
  set H : Subgroup S := F ⊓ Subgroup.centralizer ({g} : Set S) with hH
  have hHdvd : Nat.card H ∣ 16 := by
    rw [← hF16]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hH8 : Nat.card H = 8 := by
    have hc : Nat.card H ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hHdvd, by norm_num⟩
    have : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [this] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h | h | h
    · omega
    · omega
    · omega
    · exact h
    · exfalso
      have heq : H = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hF16])
      apply hgF
      have : g ∈ Subgroup.centralizer (F : Set S) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have : x ∈ H := by rw [heq]; exact hx
        exact Subgroup.mem_centralizer_singleton_iff.mp this.2
      exact Subgroup.mem_sup_left (hCF this)
  have hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy => hFab x hx.1 y hy.1
  have hHexp : ∀ x ∈ H, x * x = 1 := fun x hx => hFexp x hx.1
  have hnorm : ∀ x ∈ H, a * x * a⁻¹ ∈ H := by
    intro x hx
    have hxF : x ∈ F := hx.1
    have hxg : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hy : a * x * a⁻¹ ∈ F := (inferInstance : F.Normal).conj_mem x hxF a
    refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    set c₀ : S := a * g * a⁻¹ * g⁻¹ with hc₀
    have hgx : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = (g * x) * g⁻¹ := rfl
        _ = (x * g) * g⁻¹ := by rw [hxg]
        _ = x := by group
    have e1 : g * a * g⁻¹ = c₀⁻¹ * a := by rw [hc₀]; group
    have hcomm : c₀⁻¹ * (a * x * a⁻¹) = (a * x * a⁻¹) * c₀⁻¹ :=
      hFab _ (F.inv_mem hag) _ hy
    have key : g * (a * x * a⁻¹) * g⁻¹ = a * x * a⁻¹ := by
      calc g * (a * x * a⁻¹) * g⁻¹
          = (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
        _ = (c₀⁻¹ * a) * x * (c₀⁻¹ * a)⁻¹ := by rw [e1, hgx]
        _ = c₀⁻¹ * (a * x * a⁻¹) * c₀ := by group
        _ = (a * x * a⁻¹) * c₀⁻¹ * c₀ := by rw [hcomm]
        _ = a * x * a⁻¹ := by group
    calc (a * x * a⁻¹) * g = (g * (a * x * a⁻¹) * g⁻¹) * g := by rw [key]
      _ = g * (a * x * a⁻¹) := by group
  have hfix := card_le_card_fix_sq H hHab hHexp a hnorm
    (fun y hy => by rw [ha2, one_mul, mul_one])
  have hle : H ⊓ Subgroup.centralizer ({a} : Set S) ≤ F ⊓ Subgroup.centralizer ({a} : Set S) :=
    inf_le_inf_right _ inf_le_left
  by_cases hEq : H ⊓ Subgroup.centralizer ({a} : Set S) = F ⊓ Subgroup.centralizer ({a} : Set S)
  · apply hgF
    have hgZ : g ∈ Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) :
        Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have : x ∈ H ⊓ Subgroup.centralizer ({a} : Set S) := by rw [hEq]; exact hx
      exact Subgroup.mem_centralizer_singleton_iff.mp this.1.2
    exact hCZ hgZ
  · have hlt : Nat.card (H ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) < 4 := by
      by_contra hge
      have hge := not_lt.mp hge
      apply hEq
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ4]; exact hge)
    rw [hH8] at hfix
    have hcdvd : Nat.card (H ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) ∣ 8 := by
      rw [← hH8]
      exact Subgroup.card_dvd_of_le inf_le_left
    generalize Nat.card (H ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = c at hcdvd hfix hlt
    interval_cases c <;> first | omega | simp_all


theorem exists_comm_of_noncyclic [F.Normal] (hS : IsPGroup 2 S) (hFa : IsElemAbelian 2 F)
    (hF16 : Nat.card F = 16)
    (hZ4 : Nat.card (F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4)
    (hCZ : Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) : Set S) ≤
      F ⊔ Subgroup.zpowers a)
    (hCF : Subgroup.centralizer (F : Set S) ≤ F) (ha2 : a * a = 1)
    (hcyc : ∃ C : Subgroup (S ⧸ F), IsCyclic C ∧ C.index ≤ 2) (U : Subgroup S)
    (hU : ¬ IsCyclic (U.map (QuotientGroup.mk' F))) :
    ∃ g ∈ U, Nat.card (Subgroup.centralizer ({g} : Set S) ⊓ F : Subgroup S) ≤ 4 := by
  have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set π := QuotientGroup.mk' F with hπ
  set V := U.map π with hV
  have hP8 : Nat.card (S ⧸ F) ≤ 8 := card_quot_le_eight hS hFa hF16 hCF hcyc
  have hPp : IsPGroup 2 (S ⧸ F) := hS.to_quotient F
  have hVp : IsPGroup 2 V := hPp.to_subgroup V
  have hV3 : 3 ≤ Nat.card V := by
    by_contra hlt
    exact hU (isCyclic_of_natCard_le_two (show Nat.card V ≤ 2 by omega))
  by_cases hāV : π a ∈ V
  · obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hāV
    refine ⟨u, huU, ?_⟩
    have hk : a⁻¹ * u ∈ F := by
      have : π (a⁻¹ * u) = 1 := by rw [map_mul, map_inv, hu, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := F) _).mp this
    have hle : Subgroup.centralizer ({u} : Set S) ⊓ F ≤
        F ⊓ Subgroup.centralizer ({a} : Set S) := by
      intro y hy
      obtain ⟨hyu, hyF⟩ := hy
      refine ⟨hyF, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyu
      have hc' : y * (a⁻¹ * u)⁻¹ = (a⁻¹ * u)⁻¹ * y := hFab y hyF _ (F.inv_mem hk)
      calc y * a = y * (u * (a⁻¹ * u)⁻¹) := by group
        _ = (y * u) * (a⁻¹ * u)⁻¹ := by group
        _ = (u * y) * (a⁻¹ * u)⁻¹ := by rw [hyu']
        _ = u * (y * (a⁻¹ * u)⁻¹) := by group
        _ = u * ((a⁻¹ * u)⁻¹ * y) := by rw [hc']
        _ = (u * (a⁻¹ * u)⁻¹) * y := by group
        _ = a * y := by group
    exact (Subgroup.card_le_of_le hle).trans hZ4.le
  · have hVlt : V ≠ ⊤ := fun h => hāV (by rw [h]; exact Subgroup.mem_top _)
    have hidx : V.index ≠ 1 := fun h => hVlt (Subgroup.index_eq_one.mp h)
    have hi0 : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul := Subgroup.card_mul_index V
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hVp
    have hV4le : 4 ≤ Nat.card V := by
      by_contra hlt
      have hm1 : m ≤ 1 := by
        by_contra hm2
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      omega
    have hVi2 : 2 ≤ V.index := by omega
    have hV4 : Nat.card V = 4 := by
      have h1 : Nat.card V * 2 ≤ Nat.card V * V.index := Nat.mul_le_mul_left _ hVi2
      omega
    have hVi : V.index = 2 := by
      have h1 : 4 * V.index ≤ Nat.card V * V.index := Nat.mul_le_mul_right _ hV4le
      omega
    have hVn : V.Normal := Subgroup.normal_of_index_eq_two hVi
    have hVexp : ∀ v ∈ V, v * v = 1 := by
      intro v hv
      by_contra hne
      have hdvd' : orderOf (⟨v, hv⟩ : V) ∣ 4 := hV4 ▸ orderOf_dvd_natCard _
      have hne2 : ¬ orderOf (⟨v, hv⟩ : V) ∣ 2 := by
        intro h2
        apply hne
        have h3 : (⟨v, hv⟩ : V) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
        have h4 := congrArg Subtype.val h3
        simpa [pow_two] using h4
      have h4 : orderOf (⟨v, hv⟩ : V) = 4 := by
        generalize orderOf (⟨v, hv⟩ : V) = d at hdvd' hne2
        have hd4 : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd'
        interval_cases d <;> first | rfl | omega | simp_all
      exact hU (isCyclic_of_orderOf_eq_card (⟨v, hv⟩ : V) (h4.trans hV4.symm))
    have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
      intro x hx y hy
      have h1 := hVexp (x * y) (V.mul_mem hx hy)
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hVexp x hx)
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hVexp y hy)
      have h2 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [mul_inv_rev, hxi, hyi] at h2
      exact h2
    have hā2 : π a * π a = 1 := by rw [← map_mul, ha2, map_one]
    have hā : (π a)⁻¹ = π a := inv_eq_of_mul_eq_one_right hā2
    have hVnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v₁', hv₁'⟩ := exists_ne (1 : V)
    have hv₁V : (v₁' : S ⧸ F) ∈ V := v₁'.2
    have hv₁1 : (v₁' : S ⧸ F) ≠ 1 := fun h => hv₁' (Subtype.ext h)
    obtain ⟨v, hvV, hv1, hvc⟩ : ∃ v ∈ V, v ≠ 1 ∧ π a * v * (π a)⁻¹ = v := by
      by_cases hw : π a * (v₁' : S ⧸ F) * (π a)⁻¹ = (v₁' : S ⧸ F)
      · exact ⟨v₁', hv₁V, hv₁1, hw⟩
      · have hwV : π a * (v₁' : S ⧸ F) * (π a)⁻¹ ∈ V := hVn.conj_mem _ hv₁V (π a)
        refine ⟨(v₁' : S ⧸ F) * (π a * (v₁' : S ⧸ F) * (π a)⁻¹), V.mul_mem hv₁V hwV, ?_, ?_⟩
        · intro h
          apply hw
          have h5 : π a * (v₁' : S ⧸ F) * (π a)⁻¹ = (v₁' : S ⧸ F)⁻¹ :=
            eq_inv_of_mul_eq_one_right h
          rw [h5]
          exact inv_eq_of_mul_eq_one_right (hVexp _ hv₁V)
        · have hv₁i : (v₁' : S ⧸ F)⁻¹ = (v₁' : S ⧸ F) :=
            inv_eq_of_mul_eq_one_right (hVexp _ hv₁V)
          calc π a * ((v₁' : S ⧸ F) * (π a * (v₁' : S ⧸ F) * (π a)⁻¹)) * (π a)⁻¹
              = (π a * (v₁' : S ⧸ F) * (π a)⁻¹) *
                (π a * (π a * (v₁' : S ⧸ F) * (π a)⁻¹) * (π a)⁻¹) := by group
            _ = (π a * (v₁' : S ⧸ F) * (π a)⁻¹) *
                ((π a * π a) * (v₁' : S ⧸ F) * (π a * π a)) := by rw [hā]; group
            _ = (π a * (v₁' : S ⧸ F) * (π a)⁻¹) * (v₁' : S ⧸ F) := by rw [hā2]; group
            _ = (v₁' : S ⧸ F) * (π a * (v₁' : S ⧸ F) * (π a)⁻¹) :=
                hVcomm _ hwV _ hv₁V
    obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hvV
    refine ⟨u, huU, ?_⟩
    have hag : a * u * a⁻¹ * u⁻¹ ∈ F := by
      have : π (a * u * a⁻¹ * u⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu]
        have h6 : π a * v * (π a)⁻¹ * v⁻¹ = 1 := by rw [hvc]; group
        exact h6
      exact (QuotientGroup.eq_one_iff (N := F) _).mp this
    have hgF : u ∉ F ⊔ Subgroup.zpowers a := by
      intro hmem
      rcases mem_sup_zpowers_of_sq ha2 hmem with h7 | ⟨f, hf, rfl⟩
      · apply hv1
        rw [← hu]
        exact (QuotientGroup.eq_one_iff (N := F) _).mpr h7
      · apply hāV
        have hπf : π f = 1 := (QuotientGroup.eq_one_iff (N := F) f).mpr hf
        have : π (f * a) = π a := by
          rw [map_mul, hπf, one_mul]
        rw [← this, hu]
        exact hvV
    have := card_fix_le_four_of_commute hFa hF16 hZ4 hCZ hCF ha2 hag hgF
    rwa [inf_comm]

theorem genLE4_of_E16 [F.Normal] (hS : IsPGroup 2 S) (hFa : IsElemAbelian 2 F)
    (hF16 : Nat.card F = 16) (ha2 : a * a = 1)
    (hZ4 : Nat.card (F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) = 4)
    (hCZ : Subgroup.centralizer ((F ⊓ Subgroup.centralizer ({a} : Set S) : Subgroup S) : Set S) ≤
      F ⊔ Subgroup.zpowers a)
    (hcyc : ∃ C : Subgroup (S ⧸ F), IsCyclic C ∧ C.index ≤ 2) : GenLE4 S := by
  have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFa.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCF := centralizer_le_of_E16 hF16 hZ4 hCZ hFab ha2
  obtain ⟨C, hCcyc, hCi⟩ := hcyc
  exact genLE4_of_abelian_normal hS F inferInstance hFab hF16.le hCF
    (fun U => rank_le_two_of_cyclic_index_le_two hCcyc hCi _)
    (fun U hU => exists_comm_of_noncyclic hS hFa hF16 hZ4 hCZ hCF ha2 ⟨C, hCcyc, hCi⟩ U hU)

end L3

end CFSG.EvenSporadicStandard.Fin76b
