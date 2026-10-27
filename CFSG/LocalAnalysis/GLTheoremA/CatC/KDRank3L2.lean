module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

namespace KDRank3L2

section Abstract

variable {G : Type*} [Group G]

theorem comm_mem_of_decomp {D Φ : Subgroup G}
    (hdec : ∀ a : G, ∃ d ∈ D, ∃ φ ∈ Φ, a = d * φ)
    (hnorm : ∀ φ ∈ Φ, ∀ d ∈ D, φ * d * φ⁻¹ ∈ D)
    (hcomm : ∀ φ ∈ Φ, ∀ ψ ∈ Φ, φ * ψ = ψ * φ) (a b : G) : ⁅a, b⁆ ∈ D := by
  obtain ⟨d, hd, φ, hφ, rfl⟩ := hdec a
  obtain ⟨d', hd', ψ, hψ, rfl⟩ := hdec b
  have h1 : ψ * φ⁻¹ = φ⁻¹ * ψ := by
    have := hcomm φ hφ ψ hψ
    calc ψ * φ⁻¹ = φ⁻¹ * (φ * ψ) * φ⁻¹ := by group
      _ = φ⁻¹ * (ψ * φ) * φ⁻¹ := by rw [this]
      _ = φ⁻¹ * ψ := by group
  have key : ⁅d * φ, d' * ψ⁆ =
      d * (φ * d' * φ⁻¹) * (ψ * d⁻¹ * ψ⁻¹) * d'⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    rw [← mul_assoc ψ φ⁻¹, h1]
    group
  rw [key]
  exact D.mul_mem (D.mul_mem (D.mul_mem hd (hnorm φ hφ d' hd')) (by
    simpa using hnorm ψ hψ d⁻¹ (D.inv_mem hd))) (D.inv_mem hd')

theorem le_of_commutator_eq_self {Inn D T E : Subgroup G} [Inn.Normal]
    (hcomm : ∀ a b : G, ⁅a, b⁆ ∈ D)
    (hD2 : ∀ x ∈ D, ∀ y ∈ D, x ∉ Inn → y ∉ Inn → x * y ∈ Inn)
    (hN : E ≤ Subgroup.normalizer (T : Set G)) (hc : ⁅T, E⁆ = T) : T ≤ Inn := by
  have hTD : T ≤ D := by
    have h : ⁅T, E⁆ ≤ D := Subgroup.commutator_le.2 fun t _ e _ => hcomm t e
    rwa [hc] at h
  have h2 : ⁅T, E⁆ ≤ Inn := by
    refine Subgroup.commutator_le.2 fun t ht e he => ?_
    have hy : e * t⁻¹ * e⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hN he) t⁻¹).1 (T.inv_mem ht)
    have hcomm' : ⁅t, e⁆ = t * (e * t⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [hcomm']
    by_cases htI : t ∈ Inn
    · exact Inn.mul_mem htI (Subgroup.Normal.conj_mem ‹Inn.Normal› _ (Inn.inv_mem htI) e)
    · have hyI : e * t⁻¹ * e⁻¹ ∉ Inn := fun h => htI (by
        have h1 := Subgroup.Normal.conj_mem ‹Inn.Normal› _ h e⁻¹
        have h2 : t⁻¹ ∈ Inn := by convert h1 using 1; group
        exact (Subgroup.inv_mem_iff Inn).1 h2)
      exact hD2 t (hTD ht) _ (hTD hy) htI hyI
  rwa [hc] at h2

end Abstract

section PSL2Aut

open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction pglAction_toPGL)
open CFSG.GorensteinWalter (PSL2 PGL2 psl2FieldAut pgl2FieldAut IsOddPrimePower)

variable {K : Type} [Field K] [Finite K]

theorem psl2_comm_mem_range (a b : MulAut (PSL2 K)) : ⁅a, b⁆ ∈ (pglAction K).range := by
  refine comm_mem_of_decomp (Φ := (psl2FieldAut K).range) ?_ ?_ ?_ a b
  · intro a
    obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut a
    exact ⟨_, ⟨g, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨g, rfl⟩
    exact ⟨_, (psl2FieldAut_mul_pglAction_mul_inv σ g).symm⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]

theorem psl2_range_mul_mem_inner (hK : IsOddPrimePower (Nat.card K)) {x y : MulAut (PSL2 K)}
    (hx : x ∈ (pglAction K).range) (hy : y ∈ (pglAction K).range)
    (hxI : x ∉ inner (PSL2 K)) (hyI : y ∉ inner (PSL2 K)) : x * y ∈ inner (PSL2 K) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hJ
  have hidx : J.index = 2 := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K hK
  have hgJ : g ∉ J := fun ⟨m, hm⟩ => hxI ⟨m, by rw [← hm, pglAction_toPGL]⟩
  have hhJ : h ∉ J := fun ⟨m, hm⟩ => hyI ⟨m, by rw [← hm, pglAction_toPGL]⟩
  have hgh : g * h ∈ J := (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hgJ hhJ)
  obtain ⟨m, hm⟩ := hgh
  exact ⟨m, by rw [← map_mul, ← hm, pglAction_toPGL]⟩

theorem exists_eps (hodd : Odd (Nat.card K)) :
    ∃ ε : ℤ, (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨1, by rw [hk, hj]; push_cast; unfold Int.ModEq; omega, Or.inl rfl⟩
  · exact ⟨-1, by rw [hk, hj]; push_cast; unfold Int.ModEq; omega, Or.inr rfl⟩

theorem centralizer_involution (hK : IsOddPrimePower (Nat.card K)) {v : PSL2 K}
    (hv : orderOf v = 2) :
    ∃ (m : ℕ) (ε : ℤ), m ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ 2 * (m : ℤ) = Nat.card K - ε ∧
      Nonempty (Subgroup.centralizer ({v} : Set (PSL2 K)) ≃* DihedralGroup m) := by
  have hodd : Odd (Nat.card K) := by
    obtain ⟨r, f, -, hr, -, hq⟩ := hK
    rw [hq]; exact hr.pow
  obtain ⟨ε, hε, hε1⟩ := exists_eps hodd
  obtain ⟨m, hm2, ⟨e⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hK hε hε1 hv
  refine ⟨m, ε, ?_, hε1, hm2, ⟨e⟩⟩
  rintro rfl
  have hq3 : 3 ≤ Nat.card K := by
    obtain ⟨r, f, hr, hr', hf, hq⟩ := hK
    rw [hq]
    have : 3 ≤ r := by have := hr.two_le; rcases hr' with ⟨k, hk⟩; omega
    calc 3 ≤ r := this
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf
  rcases hε1 with rfl | rfl <;> omega

theorem not_commute_of_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKp : p ∣ Nat.card K)
    (hK : IsOddPrimePower (Nat.card K)) {v c : PSL2 K} (hv : orderOf v = 2) (hc : orderOf c = p) :
    v * c ≠ c * v := by
  intro hcomm
  obtain ⟨m, ε, hm0, hε1, hm2, ⟨e⟩⟩ := centralizer_involution hK hv
  haveI : NeZero m := ⟨hm0⟩
  have hcard : Nat.card (Subgroup.centralizer ({v} : Set (PSL2 K))) = 2 * m := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hcmem : c ∈ Subgroup.centralizer ({v} : Set (PSL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm
  have hdvd : p ∣ 2 * m := by
    rw [← hcard, ← hc]
    have := orderOf_dvd_natCard (⟨c, hcmem⟩ : Subgroup.centralizer ({v} : Set (PSL2 K)))
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨a, ha⟩ := hKp
  obtain ⟨b, hb⟩ := hdvd
  have hb' : (2 * m : ℤ) = p * b := by exact_mod_cast hb
  have ha' : (Nat.card K : ℤ) = p * a := by exact_mod_cast ha
  have h1 : (p : ℤ) ∣ 1 := by
    rcases hε1 with rfl | rfl
    · exact ⟨a - b, by linear_combination hm2 - hb' + ha'⟩
    · exact ⟨b - a, by linear_combination -hm2 + hb' - ha'⟩
  have h2 : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem card_le_four_of_sq (hK : IsOddPrimePower (Nat.card K)) (V : Subgroup (PSL2 K))
    (hV : ∀ x ∈ V, x * x = 1) : Nat.card V ≤ 4 := by
  by_cases hV1 : V = ⊥
  · subst hV1; simp
  obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hV v hvV) hv1'
  obtain ⟨m, ε, hm0, hε1, hm2, ⟨e⟩⟩ := centralizer_involution hK hv2
  haveI : NeZero m := ⟨hm0⟩
  have hVC : V ≤ Subgroup.centralizer ({v} : Set (PSL2 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hV x hx)
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV v hvV)
    have hxv : (x * v)⁻¹ = x * v := inv_eq_of_mul_eq_one_right (hV _ (V.mul_mem hx hvV))
    rw [← hxv, mul_inv_rev, hvinv, hxinv]
  set V' : Subgroup (DihedralGroup m) :=
    (V.subgroupOf (Subgroup.centralizer ({v} : Set (PSL2 K)))).map e.toMonoidHom with hV'
  have h2 : ∀ a ∈ V', a * a = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : PSL2 K) * b = 1 := hV b hb
    change e b * e b = 1
    rw [← map_mul, show b * b = 1 from Subtype.ext hb', map_one]
  have h4 := CFSG.QuasithinUnique.Setup.Family.dihedral_elemAbelian_card_le_four V' h2
  calc Nat.card V = Nat.card (V.subgroupOf (Subgroup.centralizer ({v} : Set (PSL2 K)))) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv).symm
    _ = Nat.card V' := (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom
        e.injective).toEquiv)
    _ ≤ 4 := h4

theorem psl2_no_twoSubgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKp : p ∣ Nat.card K)
    (hK : IsOddPrimePower (Nat.card K)) {A T : Subgroup (PSL2 K)} (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (hT : IsPGroup 2 T)
    (hN : A ≤ Subgroup.normalizer (T : Set (PSL2 K))) : T = ⊥ := by
  by_contra hT1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  haveI : Nontrivial (Subgroup.center ↥T) := hT.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center ↥T) := hT.to_subgroup _
  have h2dvd : 2 ∣ Nat.card (Subgroup.center ↥T) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd h (Nat.card_eq_one_iff_unique.not.2 (by
        intro ⟨hs, _⟩; exact not_subsingleton _ hs))
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2 h2dvd
  set v : PSL2 K := (((z : ↥T)) : PSL2 K) with hvdef
  have hv2 : orderOf v = 2 := by rw [hvdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hvv : v * v = 1 := by
    have h := pow_orderOf_eq_one v
    rw [hv2, sq] at h
    exact h
  let Zc : Subgroup (PSL2 K) := (Subgroup.center ↥T).map T.subtype
  have hZcT : ∀ a ∈ Zc, a ∈ T := by
    rintro _ ⟨a, -, rfl⟩; exact a.2
  have hZcomm : ∀ a ∈ Zc, ∀ t ∈ T, a * t = t * a := by
    rintro _ ⟨a, ha, rfl⟩ t ht
    have := (Subgroup.mem_center_iff.1 ha) ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm
  let V : Subgroup (PSL2 K) :=
    { carrier := {x | x ∈ Zc ∧ x * x = 1}
      one_mem' := ⟨Zc.one_mem, mul_one 1⟩
      mul_mem' := fun {a b} ⟨ha, ha2⟩ ⟨hb, hb2⟩ => ⟨Zc.mul_mem ha hb, by
        have hba : a * b = b * a := hZcomm a ha b (hZcT b hb)
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hba]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]⟩
      inv_mem' := fun {a} ⟨ha, ha2⟩ => ⟨Zc.inv_mem ha, by
        rw [← mul_inv_rev, ha2, inv_one]⟩ }
  have hvV : v ∈ V := ⟨⟨z, z.2, rfl⟩, hvv⟩
  have hinv : ∀ u ∈ A, ∀ x ∈ V, u * x * u⁻¹ ∈ V := by
    intro u hu x ⟨hxZ, hx2⟩
    refine ⟨?_, by calc u * x * u⁻¹ * (u * x * u⁻¹) = u * (x * x) * u⁻¹ := by group
                     _ = 1 := by rw [hx2]; group⟩
    have huN : u ∈ Subgroup.normalizer (T : Set (PSL2 K)) := hN hu
    have huN' : u⁻¹ ∈ Subgroup.normalizer (T : Set (PSL2 K)) := hN (A.inv_mem hu)
    have hxT : x ∈ T := hZcT x hxZ
    have hT' : u * x * u⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 huN x).1 hxT
    refine ⟨⟨u * x * u⁻¹, hT'⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    apply Subtype.ext
    show (g : PSL2 K) * (u * x * u⁻¹) = (u * x * u⁻¹) * g
    have hg : u⁻¹ * (g : PSL2 K) * u ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 huN' (g : PSL2 K)).1 g.2
      simpa using this
    have hc := hZcomm x hxZ _ hg
    calc (g : PSL2 K) * (u * x * u⁻¹) = u * ((u⁻¹ * g * u) * x) * u⁻¹ := by group
      _ = u * (x * (u⁻¹ * g * u)) * u⁻¹ := by rw [hc]
      _ = (u * x * u⁻¹) * g := by group
  have hV4 : Nat.card V ≤ 4 := card_le_four_of_sq hK V fun x hx => hx.2
  have hAlt : Nat.card V < Nat.card A := by
    rw [hAc]
    have : 3 ≤ p := by have := hp.two_le; omega
    nlinarith
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨u, w, huw, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun u : A => (⟨(u : PSL2 K) * v * (u : PSL2 K)⁻¹, hinv u u.2 v hvV⟩ : V))
    (by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card])
  have hfe : (u : PSL2 K) * v * (u : PSL2 K)⁻¹ = (w : PSL2 K) * v * (w : PSL2 K)⁻¹ :=
    congrArg Subtype.val hf
  set c : PSL2 K := (w : PSL2 K)⁻¹ * (u : PSL2 K) with hcdef
  have hcA : c ∈ A := A.mul_mem (A.inv_mem w.2) u.2
  have hc1 : c ≠ 1 := by
    intro h
    apply huw
    apply Subtype.ext
    have : (w : PSL2 K)⁻¹ * (u : PSL2 K) = 1 := h
    exact (inv_mul_eq_one.1 this).symm
  have hcv : v * c = c * v := by
    have h1 : (w : PSL2 K)⁻¹ * ((u : PSL2 K) * v * (u : PSL2 K)⁻¹) * w = v := by
      rw [hfe]; group
    calc v * c = (w : PSL2 K)⁻¹ * ((u : PSL2 K) * v * (u : PSL2 K)⁻¹) * (w : PSL2 K) * c := by
            rw [h1]
      _ = c * v := by simp only [hcdef]; group
  have hcord : orderOf c = p := orderOf_eq_prime (hA.2 c hcA) hc1
  exact not_commute_of_orderOf hp hp2 hKp hK hv2 hcord hcv

open CFSG.GorensteinWalter (psl2UpperUnipotentSubgroup mem_psl2UpperUnipotentSubgroup_iff
  psl2QuotientMap sl2UpperUnipotent sl2UpperUnipotent_mul sl2UpperUnipotent_zero
  psl2UpperUnipotentSubgroup_card)

theorem isElemAbelian_psl2Upper {p : ℕ} [Fact p.Prime] [CharP K p] :
    IsElemAbelian p (psl2UpperUnipotentSubgroup K) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (psl2Upper_mul_comm x.2 y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨s, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
  have key : ∀ n : ℕ, (psl2QuotientMap K (sl2UpperUnipotent s)) ^ n =
      psl2QuotientMap K (sl2UpperUnipotent (n • s)) := by
    intro n
    induction n with
    | zero => simp [sl2UpperUnipotent_zero]
    | succ n ih =>
      rw [pow_succ, ih, ← map_mul, sl2UpperUnipotent_mul, succ_nsmul]
  rw [key p]
  have : p • s = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [this, sl2UpperUnipotent_zero, map_one]

theorem exists_elemAbelian_sixth {p f : ℕ} (hp : p.Prime) (hKcard : Nat.card K = p ^ f)
    (hf : 6 ≤ f) : ∃ P : Subgroup (PSL2 K), IsElemAbelian p P ∧ Nat.card P = p ^ 6 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hKcard])
  have hU := isElemAbelian_psl2Upper (K := K) (p := p)
  obtain ⟨P, hPcard, -, hPU⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (H := ⊥) (L := psl2UpperUnipotentSubgroup K) (n := 6) (by simp)
    (by rw [psl2UpperUnipotentSubgroup_card, hKcard]; exact pow_dvd_pow p hf) bot_le
  exact ⟨P, isElemAbelian_mono hU hPU, hPcard⟩

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun β : MulAut G => β x) hg
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

theorem rank3Concl_psl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f)
    (hf : 6 ≤ f) (hZ : Subgroup.center (PSL2 K) = ⊥) {E : Subgroup (MulAut (PSL2 K))}
    (hE : IsElemAbelian p E) (hE0 : Nat.card ↥(E ⊓ inner (PSL2 K)) = p ^ 2) :
    Rank3Concl p (PSL2 K) E := by
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, by omega, hKcard⟩
  have hKp : p ∣ Nat.card K := by rw [hKcard]; exact dvd_pow_self p (by omega)
  refine ⟨exists_elemAbelian_sixth hp hKcard hf, ?_⟩
  intro T hT hN hc
  haveI : (inner (PSL2 K)).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hTI : T ≤ inner (PSL2 K) :=
    le_of_commutator_eq_self (D := (pglAction K).range) psl2_comm_mem_range
      (fun x hx y hy hxI hyI => psl2_range_mul_mem_inner hK hx hy hxI hyI) hN hc
  have hconj : Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) :=
    conj_injective_of_center_eq_bot hZ
  set conj : PSL2 K →* MulAut (PSL2 K) := MulAut.conj with hconjdef
  set E₀ : Subgroup (MulAut (PSL2 K)) := E ⊓ inner (PSL2 K) with hE₀
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_mono hE inf_le_left
  have hE₀r : E₀ ≤ conj.range := inf_le_right
  set A : Subgroup (PSL2 K) := E₀.comap conj with hAdef
  have hAmap : A.map conj = E₀ := Subgroup.map_comap_eq_self hE₀r
  have hAcard : Nat.card A = p ^ 2 := by
    rw [← hE0, ← hAmap, Subgroup.card_map_of_injective hconj]
  have hAel : IsElemAbelian p A := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · apply hconj
      simp only [Subgroup.coe_mul, map_mul]
      exact isElemAbelian_commute hE₀el (show conj (x : PSL2 K) ∈ E₀ from x.2)
        (show conj (y : PSL2 K) ∈ E₀ from y.2)
    · apply hconj
      rw [map_pow, map_one]
      exact hE₀el.2 _ hx
  have hT' : IsPGroup 2 (T.comap conj) := hT.comap_of_injective conj hconj
  have hAN : A ≤ Subgroup.normalizer ((T.comap conj : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
    intro u hu
    have huE : conj u ∈ E := (show conj u ∈ E₀ from hu).1
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hN huE) (conj h)
    simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
    exact this
  have hbot := psl2_no_twoSubgroup hp hp2 hKp hK hAel hAcard hT' hAN
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨m, rfl⟩ := hTI ht
  have hm : m ∈ T.comap conj := ht
  rw [hbot, Subgroup.mem_bot] at hm
  rw [hm, map_one]
  exact Subgroup.one_mem _

end PSL2Aut

end KDRank3L2

end CFSG.LocalAnalysis.GLTheoremA
