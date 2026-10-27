module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Subgroup
open scoped commutatorElement

theorem mem_normalizer_zpowers_of_conj {T : Type*} [Group T] {g d : T}
    (h : g * d * g⁻¹ = d ∨ g * d * g⁻¹ = d⁻¹) : g ∈ normalizer (zpowers d : Set T) := by
  have hinv : g⁻¹ * d * g = d ∨ g⁻¹ * d * g = d⁻¹ := by
    rcases h with h | h
    · left
      calc g⁻¹ * d * g = g⁻¹ * (g * d * g⁻¹) * g := by rw [h]
        _ = d := by group
    · right
      have : d = (g⁻¹ * d * g)⁻¹ := by
        calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
          _ = g⁻¹ * d⁻¹ * g := by rw [h]
          _ = (g⁻¹ * d * g)⁻¹ := by group
      calc g⁻¹ * d * g = (g⁻¹ * d * g)⁻¹⁻¹ := by simp
        _ = d⁻¹ := by rw [← this]
  have key : ∀ (c c' : T), c' = c⁻¹ → (c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d⁻¹) → ∀ k : ℤ,
      c * d ^ k * c' ∈ zpowers d := by
    intro c c' hc' hc k
    subst hc'
    have : c * d ^ k * c⁻¹ = (c * d * c⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply]
      simp [map_zpow]
    rw [this]
    rcases hc with hc | hc <;> rw [hc]
    · exact zpow_mem (mem_zpowers d) k
    · exact zpow_mem (inv_mem (mem_zpowers d)) k
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    exact key g g⁻¹ rfl h k
  · intro hn
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
    have hn' : n = g⁻¹ * d ^ k * g⁻¹⁻¹ := by
      calc n = g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * d ^ k * g⁻¹⁻¹ := by rw [← hk]
    rw [hn']
    exact key g⁻¹ g⁻¹⁻¹ rfl (by simpa using hinv) k

theorem stem_conj_identities {T : Type*} [Group T] (x y : T)
    (hX : ∀ g : T, g * (x * x) = (x * x) * g) (hY : ∀ g : T, g * (y * y) = (y * y) * g) :
    y⁻¹ * (x⁻¹ * y⁻¹ * x * y) * y = (x⁻¹ * y⁻¹ * x * y)⁻¹ ∧
    x⁻¹ * (x⁻¹ * y⁻¹ * x * y) * x = (x⁻¹ * y⁻¹ * x * y)⁻¹ := by
  constructor
  · calc y⁻¹ * (x⁻¹ * y⁻¹ * x * y) * y = y⁻¹ * x⁻¹ * y⁻¹ * (x * (y * y)) := by group
      _ = y⁻¹ * x⁻¹ * y⁻¹ * ((y * y) * x) := by rw [hY x]
      _ = (x⁻¹ * y⁻¹ * x * y)⁻¹ := by group
  · set u : T := y⁻¹ * x * y with hu
    have hu2 : u * u = x * x := by
      calc u * u = y⁻¹ * (x * x) * y := by rw [hu]; group
        _ = x * x := by rw [hX y⁻¹]; group
    have hui : u⁻¹ = u * (x * x)⁻¹ := by
      calc u⁻¹ = u * (u * u)⁻¹ := by group
        _ = u * (x * x)⁻¹ := by rw [hu2]
    have hxc : (x * x)⁻¹ * u = u * (x * x)⁻¹ := by
      have h := hX u
      calc (x * x)⁻¹ * u = (x * x)⁻¹ * (u * (x * x)) * (x * x)⁻¹ := by group
        _ = (x * x)⁻¹ * ((x * x) * u) * (x * x)⁻¹ := by rw [h]
        _ = u * (x * x)⁻¹ := by group
    calc x⁻¹ * (x⁻¹ * y⁻¹ * x * y) * x = (x * x)⁻¹ * u * x := by rw [hu]; group
      _ = u * (x * x)⁻¹ * x := by rw [hxc]
      _ = u⁻¹ * x := by rw [hui]
      _ = (x⁻¹ * y⁻¹ * x * y)⁻¹ := by rw [hu]; group

theorem two_involution_central_stem_bound {T : Type*} [Group T] [Finite T]
    (A : Subgroup T) (hAZ : A ≤ Subgroup.center T) (hAD : A ≤ _root_.commutator T)
    (x y : T) (hx : x * x ∈ A) (hy : y * y ∈ A) (hgen : A ⊔ Subgroup.closure {x, y} = ⊤) :
    Nat.card A ≤ 2 := by
  have hX : ∀ g : T, g * (x * x) = (x * x) * g := Subgroup.mem_center_iff.1 (hAZ hx)
  have hY : ∀ g : T, g * (y * y) = (y * y) * g := Subgroup.mem_center_iff.1 (hAZ hy)
  obtain ⟨hyd, hxd⟩ := stem_conj_identities x y hX hY
  set d : T := x⁻¹ * y⁻¹ * x * y with hd
  set D := Subgroup.zpowers d with hD
  have hxN : x ∈ normalizer (D : Set T) := by
    have h := mem_normalizer_zpowers_of_conj (g := x⁻¹) (d := d) (Or.inr (by simpa using hxd))
    simpa using (Subgroup.inv_mem _ h)
  have hyN : y ∈ normalizer (D : Set T) := by
    have h := mem_normalizer_zpowers_of_conj (g := y⁻¹) (d := d) (Or.inr (by simpa using hyd))
    simpa using (Subgroup.inv_mem _ h)
  have hAN : A ≤ normalizer (D : Set T) := fun a ha => by
    apply mem_normalizer_zpowers_of_conj
    left
    have := Subgroup.mem_center_iff.1 (hAZ ha) d
    rw [← this]; group
  have hNtop : normalizer (D : Set T) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le hAN ((Subgroup.closure_le _).2 ?_)
    rintro z (rfl | rfl)
    · exact hxN
    · simpa using hyN
  have hDn : D.Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
  have hcomm : ∀ g h : T, ⁅g, h⁆ ∈ D := by
    let π : T →* T ⧸ D := QuotientGroup.mk' D
    let S : Set (T ⧸ D) := {a | a = π x ∨ a = π y ∨ ∃ g ∈ A, a = π g}
    have hxy : π x * π y = π y * π x := by
      show (QuotientGroup.mk (x * y) : T ⧸ D) = QuotientGroup.mk (y * x)
      rw [QuotientGroup.eq]
      have : (x * y)⁻¹ * (y * x) = d⁻¹ := by rw [hd]; group
      rw [this]
      exact inv_mem (mem_zpowers d)
    have hAc : ∀ a ∈ A, ∀ g : T, π a * π g = π g * π a := fun a ha g => by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hAZ ha) g]
    have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      rintro a (rfl | rfl | ⟨a', ha', rfl⟩) b (rfl | rfl | ⟨b', hb', rfl⟩)
      · rfl
      · exact hxy
      · exact (hAc b' hb' x).symm
      · exact hxy.symm
      · rfl
      · exact (hAc b' hb' y).symm
      · exact hAc a' ha' x
      · exact hAc a' ha' y
      · exact hAc a' ha' b'
    have hclosure : Subgroup.closure S = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ A ⊔ Subgroup.closure {x, y} := by rw [hgen]; trivial
      have hmap : (A ⊔ Subgroup.closure {x, y}).map π ≤ Subgroup.closure S := by
        rw [Subgroup.map_sup, sup_le_iff]
        constructor
        · rw [Subgroup.map_le_iff_le_comap]
          intro a ha
          exact Subgroup.subset_closure (Or.inr (Or.inr ⟨a, ha, rfl⟩))
        · rw [MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨z, (rfl | rfl), rfl⟩
          · exact Subgroup.subset_closure (Or.inl rfl)
          · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      exact hmap ⟨g, hg, rfl⟩
    have hcentS : ∀ s ∈ S, ∀ b ∈ Subgroup.closure S, s * b = b * s := by
      intro s hs b hb
      have : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set (T ⧸ D)) := by
        rw [Subgroup.closure_le]
        intro t ht
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hS s hs t ht
      exact (Subgroup.mem_centralizer_iff.1 (this hb) s (Set.mem_singleton _))
    have hcomm2 : ∀ a b : T ⧸ D, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.closure S := by rw [hclosure]; trivial
      have hb : b ∈ Subgroup.closure S := by rw [hclosure]; trivial
      have : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set (T ⧸ D)) := by
        rw [Subgroup.closure_le]
        intro t ht
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hcentS t ht b hb).symm
      exact ((Subgroup.mem_centralizer_iff.1 (this ha) b (Set.mem_singleton _))).symm
    intro g h
    rw [← QuotientGroup.eq_one_iff]
    change π ⁅g, h⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm2 _ _)
  have hcommD : _root_.commutator T ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    exact hcomm g h
  have hAD' : A ≤ D := hAD.trans hcommD
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hAD' ha)
    have hc : x⁻¹ * a * x = a := by
      have := Subgroup.mem_center_iff.1 (hAZ ha) x
      rw [mul_assoc, ← this]; group
    have h1 : x⁻¹ * a * x = a⁻¹ := by
      rw [← hk]
      have : x⁻¹ * d ^ k * x = (x⁻¹ * d * x) ^ k := by
        rw [show x⁻¹ * d ^ k * x = x⁻¹ * d ^ k * x⁻¹⁻¹ by simp, ← MulAut.conj_apply,
          show x⁻¹ * d * x = x⁻¹ * d * x⁻¹⁻¹ by simp, ← MulAut.conj_apply, map_zpow]
      rw [this, hxd, inv_zpow', zpow_neg]
    have : a = a⁻¹ := hc.symm.trans h1
    calc a * a = a * a⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel a
  have hcyc : IsCyclic (A.subgroupOf D) := inferInstance
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg2 : g ^ 2 = 1 := by
    have := hsq g.1.1 g.2
    ext
    simpa [pow_two] using this
  have hcard : Nat.card (A.subgroupOf D) = orderOf g :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD').toEquiv.symm, hcard]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem two_involution_central_stem_bound' {G : Type*} [Group G] [Finite G] (T A : Subgroup G)
    (hAT : A ≤ T) (hAZ : ∀ a ∈ A, ∀ t ∈ T, t * a = a * t)
    (hAD : A ≤ (_root_.commutator (T : Subgroup G)).map T.subtype) (x y : G) (hx : x ∈ T)
    (hy : y ∈ T) (hx2 : x * x ∈ A) (hy2 : y * y ∈ A)
    (hgen : A ⊔ Subgroup.closure {x, y} = T) : Nat.card A ≤ 2 := by
  have himg : (T.subtype '' ({⟨x, hx⟩, ⟨y, hy⟩} : Set T) : Set G) = {x, y} := by
    ext z
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have h := two_involution_central_stem_bound (T := ↥T) (A.subgroupOf T)
    (fun a ha => by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hAZ a.1 ha g.1 g.2))
    (fun a ha => by
      obtain ⟨c, hc, hca⟩ := hAD ha
      have : c = a := Subtype.ext hca
      exact this ▸ hc)
    ⟨x, hx⟩ ⟨y, hy⟩ (by exact hx2) (by exact hy2) (by
      apply Subgroup.map_injective T.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAT, MonoidHom.map_closure,
        Subgroup.map_top, Subgroup.range_subtype, himg]
      exact hgen)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv] at h

theorem sylow_shape_central_kernel_bound {S E : Type*} [Group S] [Finite S] [Group E] [Finite E]
    [Group.IsPerfect E]
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p S, IsCyclic (P : Subgroup S))
    (htwo : ∀ P : Sylow 2 S, ∃ a b : (P : Subgroup S), a * a = 1 ∧ b * b = 1 ∧
      Subgroup.closure {a, b} = ⊤)
    (f : E →* S) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E) :
    Nat.card f.ker ≤ 2 := by
  have hodd' : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ T : Sylow p E,
      f.ker ⊓ (T : Subgroup E) = ⊥ := by
    intro p _ hp2 T
    have hcyc : IsCyclic ((T : Subgroup E).map f) := by
      have := hodd p hp2 (Sylow.mapSurjective hf T)
      rwa [Sylow.coe_mapSurjective] at this
    let f' : (T : Subgroup E) →* ((T : Subgroup E).map f) :=
      (f.comp (T : Subgroup E).subtype).codRestrict _ (fun x => ⟨x.1, x.2, rfl⟩)
    have hcomm : IsMulCommutative (T : Subgroup E) :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f' (by
        intro t ht
        rw [Subgroup.mem_center_iff]
        intro g
        have ht' : (t : E) ∈ f.ker := by
          have h2 : f' t = 1 := MonoidHom.mem_ker.1 ht
          exact congrArg Subtype.val h2
        exact Subtype.ext (Subgroup.mem_center_iff.1 (hker ht') g.1))
    have hd : ⁅(T : Subgroup E), (T : Subgroup E)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨b, hb⟩ : (T : Subgroup E))
        ⟨a, ha⟩)
    have hp : IsPGroup p (f.ker ⊓ (T : Subgroup E) : Subgroup E) :=
      IsPGroup.to_le T.isPGroup' inf_le_right
    have := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T _
      (inf_le_left.trans hker) hp).1
    rwa [hd, le_bot_iff] at this
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card f.ker → p = 2 := by
    intro p hp hdvd
    by_contra hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) p hdvd
    have hgE : orderOf (g : E) = p := by rw [Subgroup.orderOf_coe, hg]
    have hpg : IsPGroup p (Subgroup.zpowers (g : E)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgE, pow_one])
    obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
    have hgQ : (g : E) ∈ f.ker ⊓ (Q : Subgroup E) :=
      ⟨g.2, hQ (Subgroup.mem_zpowers _)⟩
    rw [hodd' p hp2 Q] at hgQ
    have h1 : (g : E) = 1 := hgQ
    rw [h1, orderOf_one] at hgE
    exact hp.one_lt.ne hgE
  have hpos : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have hcard : Nat.card f.ker = 2 ^ (Nat.card f.ker).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdd => hprime d hd hdd)
  have h2grp : IsPGroup 2 f.ker := IsPGroup.of_card hcard
  obtain ⟨T, hT⟩ := h2grp.exists_le_sylow
  obtain ⟨a, b, ha2, hb2, hab⟩ := htwo (Sylow.mapSurjective hf T)
  have hQ : ((Sylow.mapSurjective hf T : Sylow 2 S) : Subgroup S) = (T : Subgroup E).map f :=
    Sylow.coe_mapSurjective hf T
  have ha : a.1 ∈ (T : Subgroup E).map f := hQ ▸ a.2
  have hb : b.1 ∈ (T : Subgroup E).map f := hQ ▸ b.2
  obtain ⟨x, hxT, hxa⟩ := ha
  obtain ⟨y, hyT, hyb⟩ := hb
  have h1 : ((Sylow.mapSurjective hf T : Sylow 2 S) : Subgroup S) =
      Subgroup.closure {a.1, b.1} := by
    have := congrArg
      (Subgroup.map ((Sylow.mapSurjective hf T : Sylow 2 S) : Subgroup S).subtype) hab
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this.symm
  have hQeq : (T : Subgroup E).map f = Subgroup.closure {f x, f y} := by
    rw [hxa, hyb]
    exact hQ.symm.trans h1
  have hcl : (Subgroup.closure ({x, y} : Set E)).map f = (T : Subgroup E).map f := by
    rw [MonoidHom.map_closure, Set.image_pair, hQeq]
  refine two_involution_central_stem_bound' (T : Subgroup E) f.ker hT
    (fun a ha t ht => (Subgroup.mem_center_iff.1 (hker ha) t))
    (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T f.ker hker h2grp).2
    x y hxT hyT ?_ ?_ ?_
  · rw [MonoidHom.mem_ker, map_mul, hxa]
    exact congrArg Subtype.val ha2
  · rw [MonoidHom.mem_ker, map_mul, hyb]
    exact congrArg Subtype.val hb2
  · refine le_antisymm (sup_le hT ((Subgroup.closure_le _).2 ?_)) ?_
    · rintro z (rfl | rfl)
      · exact hxT
      · exact hyT
    · intro t ht
      have hft : f t ∈ (Subgroup.closure ({x, y} : Set E)).map f := by
        rw [hcl]; exact ⟨t, ht, rfl⟩
      obtain ⟨u, hu, hut⟩ := hft
      have hker' : t * u⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hut, mul_inv_cancel]
      have : t = (t * u⁻¹) * u := by group
      rw [this]
      exact Subgroup.mul_mem_sup hker' hu

end CFSG.QuasithinUnique.Setup.Family
