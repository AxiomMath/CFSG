module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltFix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts

theorem not_odd_card_of_isTwoQuasisimple {A : Type*} [Group A] [Finite A]
    (hA : IsTwoQuasisimple A) : ¬ Odd (Nat.card A) := by
  intro hodd
  have htop : pPrimeCore 2 A = ⊤ := by
    refine top_unique (le_pPrimeCore_of_normal_coprime normal_top ?_)
    rw [card_top]
    exact Nat.coprime_two_left.mpr hodd
  have hsub : Subsingleton (A ⧸ pPrimeCore 2 A) := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.mpr (htop ▸ mem_top _)⟩
  have hnt := LocalCores.isQuasisimple_nontrivial hA.2
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt

theorem isTwoQuasisimple_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hA : IsTwoQuasisimple A) (f : A →* B) (hf : Function.Surjective f)
    (hB : ¬ Odd (Nat.card B)) : IsTwoQuasisimple B := by
  obtain ⟨hperf, hq⟩ := hA
  refine ⟨Group.IsPerfect.ofSurjective (f := f) hf, ?_⟩
  have hle : (pPrimeCore 2 A).map f ≤ pPrimeCore 2 B := by
    have hn : (pPrimeCore 2 A).Normal := inferInstance
    refine le_pPrimeCore_of_normal_coprime (hn.map f hf) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card
  let g : A ⧸ pPrimeCore 2 A →* B ⧸ pPrimeCore 2 B :=
    QuotientGroup.map _ _ f (Subgroup.map_le_iff_le_comap.mp hle)
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hqo : Open.IsQuasisimple (A ⧸ pPrimeCore 2 A) :=
    (AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)
  rcases Quasisimple.normal_le_center_or_eq_top hqo g.ker with hc | ht
  · have hq' := Quasisimple.central_quotient hqo g.ker hc
    have e := QuotientGroup.quotientKerEquivOfSurjective g hg
    exact LocalCores.isQuasisimple_of_mulEquiv e
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mp
        ((AssemblyBPredicates.isQuasisimple_iff_open _).mpr hq'))
  · exfalso
    apply hB
    have htop : pPrimeCore 2 B = ⊤ := by
      refine top_unique fun b _ => ?_
      obtain ⟨a, ha⟩ := hg (QuotientGroup.mk b)
      have h1 : a ∈ g.ker := ht ▸ mem_top a
      rw [MonoidHom.mem_ker, ha] at h1
      exact (QuotientGroup.eq_one_iff b).mp h1
    have hcop := (pPrimeCore_coprime_card (p := 2) (G := B))
    rw [htop, card_top] at hcop
    exact Nat.coprime_two_left.mp hcop

theorem subsingleton_of_isPerfect_of_isSolvable {A : Type*} [Group A] (hA : Group.IsPerfect A)
    (hs : Group.IsSolvable A) : Subsingleton A := by
  have htop : ∀ k, derivedSeries A k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hA.commutator_eq_top]
  obtain ⟨n, hn⟩ := hs.solvable
  rw [htop] at hn
  exact ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup A) := hn ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup A) := hn ▸ mem_top b
    rw [mem_bot] at ha hb
    rw [ha, hb]⟩

@[expose] noncomputable def hatOf {G : Type} [Group G] (K J : Subgroup G) :
    Subgroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) :=
  ((J.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))).map
    (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem conj_mem (h : Config G p w v L K) {k : G} (hk : k ∈ K) : v * k * v⁻¹ ∈ K := by
  have h1 : v * k * v⁻¹ ∈ K.map (MulAut.conj v).toMonoidHom := ⟨k, hk, rfl⟩
  rwa [h.K_v] at h1

theorem v_inv (h : Config G p w v L K) : v⁻¹ = v := inv_eq_of_mul_eq_one_right h.v_sq

@[expose] noncomputable def beta (h : Config G p w v L K) : MulAut ↥K where
  toFun k := ⟨v * k * v⁻¹, h.conj_mem k.2⟩
  invFun k := ⟨v * k * v⁻¹, h.conj_mem k.2⟩
  left_inv k := Subtype.ext (by
    change v * (v * (k : G) * v⁻¹) * v⁻¹ = k
    rw [h.v_inv]
    calc v * (v * (k : G) * v) * v = (v * v) * k * (v * v) := by group
      _ = k := by rw [h.v_sq]; group)
  right_inv k := Subtype.ext (by
    change v * (v * (k : G) * v⁻¹) * v⁻¹ = k
    rw [h.v_inv]
    calc v * (v * (k : G) * v) * v = (v * v) * k * (v * v) := by group
      _ = k := by rw [h.v_sq]; group)
  map_mul' a b := Subtype.ext (by
    change v * ((a : G) * b) * v⁻¹ = v * a * v⁻¹ * (v * b * v⁻¹)
    group)

theorem beta_apply (h : Config G p w v L K) (k : ↥K) : (h.beta k : G) = v * k * v⁻¹ := rfl

theorem beta_beta (h : Config G p w v L K) (k : ↥K) : h.beta (h.beta k) = k :=
  h.beta.left_inv k

theorem mem_fixedPoints_beta (h : Config G p w v L K) {k : ↥K} :
    k ∈ fixedPoints h.beta ↔ (k : G) ∈ centralizer {v} := by
  rw [mem_fixedPoints, mem_centralizer_singleton_iff]
  constructor
  · intro hk
    have h1 : v * (k : G) * v⁻¹ = k := congrArg Subtype.val hk
    calc (k : G) * v = v * k * v⁻¹ * v := by rw [h1]
      _ = v * k := by group
  · intro hk
    apply Subtype.ext
    change v * (k : G) * v⁻¹ = k
    rw [← hk]
    group

@[expose] noncomputable def tau (h : Config G p w v L K) : MulAut (↥K ⧸ pPrimeCore 2 ↥K) :=
  oddAut h.beta

theorem isTwoComponentIn_hat (h : Config G p w v L K) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (K ⊓ centralizer {v})) :
    IsTwoComponentIn (hatOf K J) (fixedPoints (quotAut h.tau)) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJv : J ≤ centralizer {v} := hJ.1.trans inf_le_right
  have hJx : J.subgroupOf K ≤ fixedPoints h.beta := fun x hx =>
    h.mem_fixedPoints_beta.mpr (hJv (mem_subgroupOf.mp hx))
  have hsubx : ((J.subgroupOf K).subgroupOf (fixedPoints h.beta)).IsSubnormal := by
    let ψ : ↥(K ⊓ centralizer ({v} : Set G)) →* ↥(fixedPoints h.beta) :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, h.mem_fixedPoints_beta.mpr x.2.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hψ : Function.Surjective ψ := by
      rintro ⟨⟨k, hk⟩, hkf⟩
      exact ⟨⟨k, hk, h.mem_fixedPoints_beta.mp hkf⟩, rfl⟩
    have hmap : (J.subgroupOf (K ⊓ centralizer {v})).map ψ =
        (J.subgroupOf K).subgroupOf (fixedPoints h.beta) := by
      ext y
      rw [mem_map, mem_subgroupOf, mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨(y : ↥K), (y : ↥K).2, h.mem_fixedPoints_beta.mp y.2⟩, hy, rfl⟩
    rw [← hmap]
    exact hJ.2.1.map hψ
  set Jt := (J.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) with hJt
  have hsubY : (Jt.subgroupOf (fixedPoints h.tau)).IsSubnormal :=
    isSubnormal_map_oddAut h.beta h.beta_beta hJx hsubx
  have hJY : Jt ≤ fixedPoints h.tau := by
    rintro _ ⟨x, hx, rfl⟩
    change oddAut h.beta (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [oddAut_mk, mem_fixedPoints.mp (hJx hx)]
  have hle : hatOf K J ≤ fixedPoints (quotAut h.tau) := by
    rintro _ ⟨y, hy, rfl⟩
    change quotAut h.tau (QuotientGroup.mk y) = QuotientGroup.mk y
    rw [quotAut_mk, mem_fixedPoints.mp (hJY hy)]
  refine ⟨hle, isSubnormal_map_quotAut h.tau hJY hsubY, ?_⟩
  let f : ↥J →* ↥(hatOf K J) :=
    { toFun := fun x => ⟨QuotientGroup.mk (QuotientGroup.mk (⟨x, hJK x.2⟩ : ↥K)),
        ⟨_, ⟨⟨x, hJK x.2⟩, x.2, rfl⟩, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  refine isTwoQuasisimple_of_surjective hJ.2.2 f hf fun hodd => ?_
  have hJperf : Group.IsPerfect ↥J := hJ.2.2.1
  have hss : Subsingleton ↥(hatOf K J) :=
    subsingleton_of_isPerfect_of_isSolvable (Group.IsPerfect.ofSurjective (f := f) hf)
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hJtZ : Jt ≤ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    intro y hy
    have h1 : (⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩⟩ : ↥(hatOf K J)) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff y).mp (congrArg Subtype.val h1)
  let g : ↥J →* ↥Jt :=
    { toFun := fun x => ⟨QuotientGroup.mk (⟨x, hJK x.2⟩ : ↥K), ⟨⟨x, hJK x.2⟩, x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : Function.Surjective g := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hJtss : Subsingleton ↥Jt :=
    subsingleton_of_isPerfect_of_isSolvable (Group.IsPerfect.ofSurjective (f := g) hg)
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp (hJtZ b.2) a))
  have hJO : ∀ x : ↥J, (⟨x, hJK x.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := fun x => by
    have h1 : g x = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
  apply not_odd_card_of_isTwoQuasisimple hJ.2.2
  have hinj : Function.Injective fun x : ↥J =>
      (⟨⟨x, hJK x.2⟩, hJO x⟩ : ↥(pPrimeCore 2 ↥K)) := fun a b hab =>
    Subtype.ext (congrArg (fun y : ↥(pPrimeCore 2 ↥K) => ((y : ↥K) : G)) hab)
  have hdvd : Nat.card ↥J ∣ Nat.card ↥(pPrimeCore 2 ↥K) := by
    let φ : ↥J →* ↥(pPrimeCore 2 ↥K) :=
      { toFun := fun x => ⟨⟨x, hJK x.2⟩, hJO x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := hinj
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card))) hdvd

end Config

end CFSG.ComponentClassification.HarrisLit.L35
