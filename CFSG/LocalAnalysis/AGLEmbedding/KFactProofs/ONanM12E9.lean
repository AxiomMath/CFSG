module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12Cover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanKHyp
public import CFSG.CharacterTheory.Burnside
public import Certificates.Certificate9682
public import CFSG.RankThree.PartTwo.KFacts.KS1515M12Cover

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Cover

open CFSG.AGLEmbedding.KFactProofs.M12Z2 CFSG.Blueprint CFSG.Sporadic.Mathieu
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.CGT.PushingUpLit.CGT6M
  CFSG.Sporadic.Bridge

abbrev M12Grp : Type := NativeSporadic.M12

theorem not_autIn_perm_three {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (e : autIn ⊤ B ≃* Equiv.Perm (Fin 3)) {n s : G}
    (hn : n ∈ Subgroup.normalizer (B : Set G)) (hs : s ∈ B)
    (hne : n ^ 6 * s * (n ^ 6)⁻¹ ≠ s) : False := by
  have hσ : B.normalizerMonoidHom ⟨n, hn⟩ ∈ autIn ⊤ B := mem_autIn_iff.2 ⟨n, hn, trivial, rfl⟩
  let σ : autIn ⊤ B := ⟨_, hσ⟩
  have hcard : Nat.card (autIn ⊤ B) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have h6 : σ ^ 6 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h6' : (B.normalizerMonoidHom ⟨n, hn⟩) ^ 6 = 1 := by
    simpa using congrArg Subtype.val h6
  have h := congrArg (fun φ : MulAut B => ((φ ⟨s, hs⟩ : B) : G)) h6'
  rw [← map_pow] at h
  exact hne (by simpa [normalizerMonoidHom_apply_coe] using h)

theorem isSolvable_of_not_dvd (Y : Subgroup M12Grp)
    (h5 : ¬ 5 ∣ Nat.card Y) (h11 : ¬ 11 ∣ Nat.card Y) : Group.IsSolvable Y := by
  have hdvd : Nat.card Y ∣ 95040 := card_M12 ▸ Subgroup.card_subgroup_dvd_card Y
  have h1 : Nat.card Y ∣ 19008 := by
    refine Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm (n := 5) ?_
    simpa using hdvd
  have h2 : Nat.card Y ∣ 1728 := by
    refine Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11).symm (n := 11) ?_
    simpa using h1
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 (show Nat.card Y ∣ 2 ^ 6 * 3 ^ 3 by simpa using h2)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype Y := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem eq_top_of_order
    {Y : Subgroup M12Grp} (hu : (⟨m12CoverU, m12CoverU_mem⟩ : M12Grp) ∈ Y)
    (hv : (⟨m12CoverV, m12CoverV_mem⟩ : M12Grp) ∈ Y) {g : M12Grp} (hg : g ∈ Y)
    (hord : orderOf g = 5 ∨ orderOf g = 11) : Y = ⊤ := by
  have hcore := m12Cover_core g.2 (by rwa [Subgroup.orderOf_coe])
  have hmap : (Subgroup.closure ({⟨m12CoverU, m12CoverU_mem⟩, ⟨m12CoverV, m12CoverV_mem⟩, g} :
      Set M12Grp)).map NativeSporadic.M12.subtype =
      Subgroup.closure ({m12CoverU, m12CoverV, (g : Equiv.Perm (Fin 12))} :
        Set (Equiv.Perm (Fin 12))) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq]
  have hle : Subgroup.closure ({⟨m12CoverU, m12CoverU_mem⟩, ⟨m12CoverV, m12CoverV_mem⟩, g} :
      Set M12Grp) ≤ Y := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | rfl | rfl)
    · exact hu
    · exact hv
    · exact hg
  refine top_unique fun w _ => hle ?_
  have hw : (w : Equiv.Perm (Fin 12)) ∈ Subgroup.map NativeSporadic.M12.subtype
      (Subgroup.closure ({⟨m12CoverU, m12CoverU_mem⟩, ⟨m12CoverV, m12CoverV_mem⟩, g} :
        Set M12Grp)) := by
    rw [hmap]
    exact hcore w.2
  obtain ⟨w', hw', hww'⟩ := hw
  have : w' = w := Subtype.ext hww'
  exact this ▸ hw'

theorem main_III
    {B X : Subgroup M12Grp}
    (hu : (⟨m12CoverU, m12CoverU_mem⟩ : M12Grp) ∈ B)
    (hv : (⟨m12CoverV, m12CoverV_mem⟩ : M12Grp) ∈ B) [hperf : Group.IsPerfect X] (hX : X ≠ ⊥)
    (hN : B ≤ Subgroup.normalizer (X : Set M12Grp)) : X = ⊤ := by
  have hXY : X ≤ X ⊔ B := le_sup_left
  have hBY : B ≤ X ⊔ B := le_sup_right
  have hYN : X ⊔ B ≤ Subgroup.normalizer (X : Set M12Grp) :=
    sup_le Subgroup.le_normalizer hN
  have hYtop : X ⊔ B = ⊤ := by
    by_contra hne
    have hno : ∀ g ∈ X ⊔ B, orderOf g ≠ 5 ∧ orderOf g ≠ 11 := fun g hg =>
      ⟨fun h5 => hne (eq_top_of_order (hBY hu) (hBY hv) hg (Or.inl h5)),
        fun h11 => hne (eq_top_of_order (hBY hu) (hBY hv) hg (Or.inr h11))⟩
    have hndvd : ∀ p : ℕ, p.Prime → (p = 5 ∨ p = 11) →
        ¬ p ∣ Nat.card (X ⊔ B : Subgroup M12Grp) := by
      intro p hp hp' hdvd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hxo := hno x x.2
      rcases hp' with rfl | rfl
      · exact hxo.1 (by rw [Subgroup.orderOf_coe]; exact hx)
      · exact hxo.2 (by rw [Subgroup.orderOf_coe]; exact hx)
    have hsolv := isSolvable_of_not_dvd (X ⊔ B) (hndvd 5 (by norm_num) (Or.inl rfl))
      (hndvd 11 (by norm_num) (Or.inr rfl))
    have hXsolv : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY)
    have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hX
    exact Group.IsPerfect.not_isSolvable X hXsolv
  have hnorm : X.Normal := Subgroup.normalizer_eq_top_iff.1 (top_unique (hYtop ▸ hYN))
  exact (fam_m12_simplicity.2.2.eq_bot_or_eq_top_of_normal X).resolve_left hX

@[expose] def m12HeisK : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure ({m12HeisA, m12HeisB} : Set (Equiv.Perm (Fin 12)))

theorem m12HeisC_mem_K : m12HeisC ∈ m12HeisK := by
  have ha : m12HeisA ∈ m12HeisK := Subgroup.subset_closure (by simp)
  have hb : m12HeisB ∈ m12HeisK := Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem mem_m12HeisK_iff (x : Equiv.Perm (Fin 12)) :
    x ∈ m12HeisK ↔ x ∈ heisList m12HeisA m12HeisB m12HeisC :=
  mem_closure_pair_iff_mem_heisList m12Heis_pow_three.1 m12Heis_pow_three.2 m12HeisC_mem_K
    m12Heis_stable x

theorem card_m12HeisK : Nat.card m12HeisK = 27 :=
  card_closure_pair_of_heisList m12Heis_pow_three.1 m12Heis_pow_three.2 m12HeisC_mem_K
    m12Heis_nodup m12Heis_stable

theorem m12HeisK_le : m12HeisK ≤ NativeSporadic.M12 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (rfl | rfl)
  · exact m12HeisA_mem
  · exact m12HeisB_mem

theorem m12HeisC_mem : m12HeisC ∈ NativeSporadic.M12 := m12HeisK_le m12HeisC_mem_K

@[expose] def m12HeisKG : Subgroup M12Grp := m12HeisK.subgroupOf NativeSporadic.M12

theorem card_m12HeisKG : Nat.card m12HeisKG = 27 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe m12HeisK_le).toEquiv).trans card_m12HeisK

theorem m12HeisKG_index : ¬ 3 ∣ m12HeisKG.index := by
  have h := m12HeisKG.card_mul_index
  rw [card_m12HeisKG, card_M12] at h
  have : m12HeisKG.index = 3520 := by omega
  rw [this]
  norm_num

noncomputable def m12HeisSylow : Sylow 3 M12Grp :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (IsPGroup.of_card (p := 3) (n := 3) (by rw [card_m12HeisKG]; norm_num) :
    IsPGroup 3 m12HeisKG).toSylow m12HeisKG_index

theorem exists_conj_le_K {B : Subgroup M12Grp}
    (hB : Nat.card B = 9) : ∃ g : M12Grp, B.map (MulAut.conj g⁻¹).toMonoidHom ≤ m12HeisKG := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨Q, hBQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12Grp m12HeisSylow Q
  refine ⟨g, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbQ : b ∈ (Q : Subgroup M12Grp) := hBQ hb
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbQ
  obtain ⟨k, hk, hkb⟩ := hbQ
  have hk' : k ∈ m12HeisKG := by simpa [m12HeisSylow] using hk
  have : (MulAut.conj g⁻¹).toMonoidHom b = k := by
    rw [← hkb]
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hk'

theorem m12E9SetEq_iff {L S : List (Equiv.Perm (Fin 12))} (h : m12E9SetEq L S = true) (z) :
    z ∈ L ↔ z ∈ S := by
  simp only [m12E9SetEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun hz => h.1 z hz, fun hz => h.2 z hz⟩

theorem mem_M12_of_mem_E9 {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    {s : Equiv.Perm (Fin 12)}
    (hs : s ∈ (List.range 3).flatMap fun i => (List.range 3).map fun k => g ^ i * m12HeisC ^ k) :
    s ∈ NativeSporadic.M12 := by
  simp only [List.mem_flatMap, List.mem_map] at hs
  obtain ⟨i, -, k, -, rfl⟩ := hs
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hg _) (Subgroup.pow_mem _ m12HeisC_mem _)

theorem classify {B : Subgroup M12Grp} [IsMulCommutative B] (hK : B ≤ m12HeisKG)
    (hcard : Nat.card B = 9) (hcl : m12E9ClassOK = true) :
    ∃ S ∈ [m12E9II, m12E9I, m12E9III, m12E9IIIp],
      ∀ b : M12Grp, b ∈ B ↔ (b : Equiv.Perm (Fin 12)) ∈ S := by
  classical
  have hBH : ∀ b ∈ B, (b : Equiv.Perm (Fin 12)) ∈ heisList m12HeisA m12HeisB m12HeisC :=
    fun b hb => (mem_m12HeisK_iff _).1 (hK hb)
  have : Fintype B := Fintype.ofFinite B
  let ι : B → Equiv.Perm (Fin 12) := fun b => ((b : M12Grp) : Equiv.Perm (Fin 12))
  have hι : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
  have hcardB : (Finset.univ.image ι).card = 9 := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨x, hxB, hxZ⟩ : ∃ x ∈ B, (x : Equiv.Perm (Fin 12)) ∉
      [1, m12HeisC, m12HeisC * m12HeisC] := by
    by_contra hcon
    have hcon' : ∀ x ∈ B, (x : Equiv.Perm (Fin 12)) ∈ [1, m12HeisC, m12HeisC * m12HeisC] :=
      fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩
    have hsub : Finset.univ.image ι ⊆ ([1, m12HeisC, m12HeisC * m12HeisC] :
        List (Equiv.Perm (Fin 12))).toFinset := by
      intro z hz
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hz
      exact List.mem_toFinset.2 (hcon' b b.2)
    have h1 := Finset.card_le_card hsub
    have h2 : ([1, m12HeisC, m12HeisC * m12HeisC] :
        List (Equiv.Perm (Fin 12))).toFinset.card ≤ 3 :=
      (List.toFinset_card_le _).trans (by simp)
    omega
  have hxH := hBH x hxB
  have hrow := List.all_eq_true.1 hcl (x : Equiv.Perm (Fin 12)) hxH
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨hnd, hlen⟩, hS⟩ := hrow.resolve_left hxZ
  have hsub : Finset.univ.image ι ⊆ (m12E9Cent (x : Equiv.Perm (Fin 12))).toFinset := by
    intro z hz
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hz
    refine List.mem_toFinset.2 ?_
    simp only [m12E9Cent, List.mem_filter, decide_eq_true_eq]
    refine ⟨hBH b b.2, ?_⟩
    have := mul_comm' b ⟨x, hxB⟩
    exact congrArg (fun w : B => ((w : M12Grp) : Equiv.Perm (Fin 12))) this
  have hcardC : (m12E9Cent (x : Equiv.Perm (Fin 12))).toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : Finset.univ.image ι = (m12E9Cent (x : Equiv.Perm (Fin 12))).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmemC : ∀ b : M12Grp, b ∈ B ↔ (b : Equiv.Perm (Fin 12)) ∈
      m12E9Cent (x : Equiv.Perm (Fin 12)) := by
    intro b
    constructor
    · intro hb
      have : ι ⟨b, hb⟩ ∈ Finset.univ.image ι := Finset.mem_image_of_mem _ (Finset.mem_univ _)
      rw [heq] at this
      exact List.mem_toFinset.1 this
    · intro hb
      have : (b : Equiv.Perm (Fin 12)) ∈ Finset.univ.image ι := by
        rw [heq]; exact List.mem_toFinset.2 hb
      obtain ⟨b', -, hb'⟩ := Finset.mem_image.1 this
      have : (b' : M12Grp) = b := Subtype.ext hb'
      exact this ▸ b'.2
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hS with ((h | h) | h) | h
  · exact ⟨m12E9II, Or.inl rfl, fun b => (hmemC b).trans (m12E9SetEq_iff h _)⟩
  · exact ⟨m12E9I, Or.inr (Or.inl rfl), fun b => (hmemC b).trans (m12E9SetEq_iff h _)⟩
  · exact ⟨m12E9III, Or.inr (Or.inr (Or.inl rfl)), fun b => (hmemC b).trans (m12E9SetEq_iff h _)⟩
  · exact ⟨m12E9IIIp, Or.inr (Or.inr (Or.inr rfl)), fun b => (hmemC b).trans (m12E9SetEq_iff h _)⟩

theorem m12E9AutOK_iff {S : List (Equiv.Perm (Fin 12))} {n : Equiv.Perm (Fin 12)}
    (h : m12E9AutOK S n = true) :
    (∀ s ∈ S, n * s * n⁻¹ ∈ S ∧ n⁻¹ * s * n ∈ S) ∧ ∃ s ∈ S, n ^ 6 * s * (n ^ 6)⁻¹ ≠ s := by
  simpa only [m12E9AutOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] using h

theorem main_in_K
    {B X : Subgroup M12Grp}
    (hK : B ≤ m12HeisKG) (h : KHyp B X) : X = ⊤ := by
  have hall := h
  obtain ⟨⟨hcomm, hexp⟩, hcard, ⟨e⟩, hperf, hX, hN⟩ := h
  have hf := Certificates.certificate9682
  simp only [m12E9Facts, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcl, hII⟩, hI⟩, hN0u⟩, hN0v⟩, hUIII⟩, hVIII⟩, hw2⟩, hw1⟩, hw0⟩ := hf
  have : IsMulCommutative B := hcomm
  obtain ⟨S, hSmem, hS⟩ := classify hK hcard hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSmem
  have hnm : ∀ n : Equiv.Perm (Fin 12), ∀ w : List (ℕ × Bool), wordProd m12Gen w = n →
      n ∈ NativeSporadic.M12 := fun n w hw => hw ▸ wordProd_mem m12Gen_mem w
  have aut : ∀ (S : List (Equiv.Perm (Fin 12))) (n : Equiv.Perm (Fin 12)),
      (∀ b : M12Grp, b ∈ B ↔ (b : Equiv.Perm (Fin 12)) ∈ S) → n ∈ NativeSporadic.M12 →
      (∀ s ∈ S, s ∈ NativeSporadic.M12) → m12E9AutOK S n = true → False := by
    intro S n hSB hn hSM hOK
    obtain ⟨hnorm, s, hs, hsne⟩ := m12E9AutOK_iff hOK
    have hnN : (⟨n, hn⟩ : M12Grp) ∈ Subgroup.normalizer (B : Set M12Grp) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      rw [hSB b, hSB (⟨n, hn⟩ * b * ⟨n, hn⟩⁻¹)]
      change _ ↔ n * (b : Equiv.Perm (Fin 12)) * n⁻¹ ∈ S
      constructor
      · exact fun h1 => (hnorm _ h1).1
      · intro h1
        simpa [mul_assoc] using (hnorm _ h1).2
    refine not_autIn_perm_three e hnN (s := ⟨s, hSM s hs⟩) ((hSB _).2 hs) ?_
    intro heq
    exact hsne (congrArg (fun w : M12Grp => (w : Equiv.Perm (Fin 12))) heq)
  rcases hSmem with rfl | rfl | rfl | rfl
  · exact (aut _ _ hS (hnm _ _ hw2) (fun s hs => mem_M12_of_mem_E9 m12HeisA_mem hs) hII).elim
  · exact (aut _ _ hS (hnm _ _ hw1) (fun s hs => mem_M12_of_mem_E9
      (Subgroup.mul_mem _ m12HeisA_mem m12HeisB_mem) hs) hI).elim
  · have := hperf
    exact main_III ((hS _).2 hUIII) ((hS _).2 hVIII) hX hN
  · obtain ⟨n0, hn0e⟩ : ∃ n0 : M12Grp, (n0 : Equiv.Perm (Fin 12)) = m12E9N0 :=
      ⟨⟨m12E9N0, hnm _ _ hw0⟩, rfl⟩
    obtain ⟨u0, hu0e⟩ : ∃ u0 : M12Grp, (u0 : Equiv.Perm (Fin 12)) = m12CoverU :=
      ⟨⟨m12CoverU, m12CoverU_mem⟩, rfl⟩
    obtain ⟨v0, hv0e⟩ : ∃ v0 : M12Grp, (v0 : Equiv.Perm (Fin 12)) = m12CoverV :=
      ⟨⟨m12CoverV, m12CoverV_mem⟩, rfl⟩
    have hu1 : n0⁻¹ * u0 * n0 ∈ B := (hS _).2 (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn0e, hu0e]; exact hN0u)
    have hv1 : n0⁻¹ * v0 * n0 ∈ B := (hS _).2 (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn0e, hv0e]; exact hN0v)
    have hmap := KHyp.map (MulAut.conj n0) hall
    obtain ⟨-, -, -, hperf2, hX2, hN2⟩ := hmap
    have hu' : u0 ∈ B.map (MulAut.conj n0).toMonoidHom :=
      ⟨n0⁻¹ * u0 * n0, hu1, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hv' : v0 ∈ B.map (MulAut.conj n0).toMonoidHom :=
      ⟨n0⁻¹ * v0 * n0, hv1, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hu0 : u0 = ⟨m12CoverU, m12CoverU_mem⟩ := Subtype.ext hu0e
    have hv0 : v0 = ⟨m12CoverV, m12CoverV_mem⟩ := Subtype.ext hv0e
    rw [hu0] at hu'
    rw [hv0] at hv'
    exact eq_top_of_map_eq_top (MulAut.conj n0) (main_III hu' hv' hX2 hN2)

end CFSG.AGLEmbedding.KFactProofs.M12Cover

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.AGLEmbedding.KFactProofs.M12Cover

theorem ks1515M12Cover :
    KS1515M12Cover := by
  intro M _ _ ⟨e⟩ B X hB hcard haut hperf hX hN
  have h := KHyp.map e (show KHyp B X from ⟨hB, hcard, haut, hperf, hX, hN⟩)
  obtain ⟨g, hg⟩ := exists_conj_le_K (B := B.map e.toMonoidHom) h.2.1
  have h' := KHyp.map (MulAut.conj g⁻¹) h
  exact eq_top_of_map_eq_top e (eq_top_of_map_eq_top _ (main_in_K hg h'))

end CFSG.RankThree.PartTwo.KFacts
