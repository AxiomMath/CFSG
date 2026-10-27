module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNOTests
public import CFSG.Sporadic.HNOddCore.SylD
public import CFSG.Sporadic.HNOddCore.SixA

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open Subgroup Equiv CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

section Arrays

variable {n : ℕ}

theorem rep_prodA {l : List (Array ℕ)} {gs : List (Perm (Fin n))}
    (h : List.Forall₂ (Rep n) l gs) : Rep n (prodA n l) gs.prod := by
  induction h with
  | nil => exact rep_idA
  | cons ha _ ih => exact rep_compA ha ih

theorem rep_powA {a : Array ℕ} {g : Perm (Fin n)} (h : Rep n a g) (m : ℕ) :
    Rep n (powA n a m) (g ^ m) := by
  have : List.Forall₂ (Rep n) (List.replicate m a) (List.replicate m g) := by
    induction m with
    | zero => exact .nil
    | succ m ih => exact .cons h ih
  have h' := rep_prodA this
  rwa [List.prod_replicate] at h'

theorem orderOf_of_ord4A {y : Array ℕ} {g : Perm (Fin n)} (h : Rep n y g)
    (hy : ord4A n y = true) : orderOf g = 4 := by
  simp only [ord4A, Bool.and_eq_true, Bool.not_eq_true'] at hy
  obtain ⟨h1, h2⟩ := hy
  have h2' : g * g * (g * g) = 1 :=
    (eqA_iff (rep_compA (rep_compA h h) (rep_compA h h)) rep_idA).1 h2
  have h1' : g * g ≠ 1 := fun e => by
    rw [(eqA_iff (rep_compA h h) rep_idA).2 e] at h1
    exact Bool.noConfusion h1
  refine orderOf_eq_four (by rwa [pow_two]) ?_
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  exact h2'

theorem isInvolA_of_rep {x : Array ℕ} {g : Perm (Fin n)} (h : Rep n x g) (h1 : g ≠ 1)
    (h2 : g * g = 1) : isInvolA n x = true := by
  simp only [isInvolA, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, (eqA_iff (rep_compA h h) rep_idA).2 h2⟩
  by_contra hne
  rw [Bool.not_eq_false] at hne
  exact h1 ((eqA_iff h rep_idA).1 hne)

variable {C : Type*} [Group C] (ρ : C →* Perm (Fin n))

theorem regsFrom_rep : ∀ (prog : List (ℕ × ℕ)) (R : Array (Array ℕ)),
    progOK R.size prog = true → (∀ i < R.size, ∃ h : C, Rep n R[i]! (ρ h)) →
    ∀ i < (regsFrom n R prog).size, ∃ h : C, Rep n (regsFrom n R prog)[i]! (ρ h)
  | [], _, _, hR => hR
  | ij :: rest, R, hp, hR => by
    simp only [progOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨h1, h2⟩, hrest⟩ := hp
    show ∀ i < (regsFrom n (R.push (compA n R[ij.1]! R[ij.2]!)) rest).size, _
    refine regsFrom_rep rest _ (by rw [Array.size_push]; exact hrest) fun i hi => ?_
    rw [Array.size_push] at hi
    by_cases hlt : i < R.size
    · rw [getElem!_pos _ i (by rw [Array.size_push]; omega), Array.getElem_push_lt hlt,
        ← getElem!_pos R i hlt]
      exact hR i hlt
    · obtain rfl : i = R.size := by omega
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      obtain ⟨a, ha⟩ := hR ij.1 h1
      obtain ⟨b, hb⟩ := hR ij.2 h2
      exact ⟨a * b, by rw [map_mul]; exact rep_compA ha hb⟩

theorem regsA_rep {S : Array (Array ℕ)} {g : ℕ → C} (hS : ∀ s < S.size, Rep n S[s]! (ρ (g s)))
    (hV : ∀ s < S.size, validA n S[s]! = true) {prog : List (ℕ × ℕ)}
    (hp : progOK (2 * S.size) prog = true) :
    ∀ i < (regsA n S prog).size, ∃ h : C, Rep n (regsA n S prog)[i]! (ρ h) := by
  refine regsFrom_rep ρ prog _ (by rwa [Array.size_append, Array.size_map, ← two_mul]) ?_
  intro i hi
  rw [Array.size_append, Array.size_map] at hi
  by_cases hlt : i < S.size
  · refine ⟨g i, ?_⟩
    rw [getElem!_pos _ i (by rw [Array.size_append, Array.size_map]; omega),
      Array.getElem_append_left hlt, ← getElem!_pos S i hlt]
    exact hS i hlt
  · have hj : i - S.size < S.size := by omega
    refine ⟨(g (i - S.size))⁻¹, ?_⟩
    rw [getElem!_pos _ i (by rw [Array.size_append, Array.size_map]; omega),
      Array.getElem_append_right (by omega), Array.getElem_map, ← getElem!_pos S _ hj, map_inv]
    exact rep_inv_of_isInvA (hS _ hj) (hV _ hj)

end Arrays

theorem aCheck_spec {C : Type*} [Group C] {n : ℕ} (ρ : C →* Perm (Fin n))
    {S : Array (Array ℕ)} {g : ℕ → C} (hS : ∀ s < S.size, Rep n S[s]! (ρ (g s)))
    {prog : List (ℕ × ℕ)} {pregs : List ℕ} {pool : Array (ℕ × ℕ)} {ps : List ℕ} {N : ℕ}
    {wits : Array AWit} (hc : aCheck n S prog pregs pool ps N wits = true) :
    ∃ Q : Subgroup (Perm (Fin n)), Q ≤ ρ.range ∧ Nat.card Q = N ∧
      ∀ b : C, ρ b ∈ Q → ρ b * ρ b = 1 → ρ b ≠ 1 →
        ∃ W ∈ closure {y | ∃ h₁ h₂ : C, y = ⁅b, ⁅h₁, h₂⁆⁆}, 4 ∣ orderOf W := by
  simp only [aCheck, aLoop, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hV, hp⟩, hpregs⟩, hpool⟩, hcs⟩, hps⟩, hen⟩, hsize⟩, -⟩, hall⟩ := hc
  rw [List.all_eq_true] at hpregs hps
  rw [Array.all_eq_true_iff_forall_mem] at hpool
  have hRrep := regsA_rep ρ hS (fun s hs => allLt_spec hV hs) hp
  have hps' : ∀ p ∈ ps, p < n := fun p hp => of_decide_eq_true (hps p hp)
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps' hen
  refine ⟨closure (permsA n ((pregs.map fun i => (regsA n S prog)[i]!).toArray)), ?_,
    hcard.trans hsize, ?_⟩
  ·
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_ofPred_eq, List.size_toArray, List.length_map] at hk
    have hmemk : pregs[k]! ∈ pregs := by
      rw [getElem!_pos pregs k hk]
      exact List.getElem_mem hk
    have hk' : pregs[k]! < (regsA n S prog).size := of_decide_eq_true (hpregs _ hmemk)
    obtain ⟨h, hh⟩ := hRrep _ hk'
    have hgk : ((pregs.map fun i => (regsA n S prog)[i]!).toArray)[k]! =
        (regsA n S prog)[pregs[k]!]! := by
      rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
        ← getElem!_pos pregs k hk]
    refine ⟨h, ?_⟩
    beta_reduce
    rw [hgk, permOfArr_eq_of_rep hh]
  · intro b hbQ hb2 hb1
    obtain ⟨i, hi, hix⟩ := (hmem (ρ b)).1 hbQ
    set cP := enumBfs n ((pregs.map fun i => (regsA n S prog)[i]!).toArray) ps (2 * N)
    have hxrep : Rep n cP.pts[i]! (ρ b) := hix ▸ rep_of_validA (hval i hi)
    have hxv := hval i hi
    have hwk := allLt_spec hall (show i < N by omega)
    set cs := pool.map fun gh => commutatorA n (regsA n S prog)[gh.1]! (regsA n S prog)[gh.2]!
    have hcsrep : ∀ f, ∃ h₁ h₂ : C, f < cs.size → Rep n cs[f]! (ρ ⁅h₁, h₂⁆) ∧
        validA n cs[f]! = true := by
      intro f
      by_cases hf : f < cs.size
      · have hf' : f < pool.size := by simpa [cs] using hf
        have hgh := hpool pool[f]! (by rw [getElem!_pos pool f hf']; exact Array.getElem_mem _)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hgh
        obtain ⟨⟨⟨h1, h2⟩, hv1⟩, hv2⟩ := hgh
        obtain ⟨a, ha⟩ := hRrep _ h1
        obtain ⟨c, hc⟩ := hRrep _ h2
        refine ⟨a, c, fun _ => ⟨?_, allLt_spec hcs hf⟩⟩
        have e : cs[f]! = commutatorA n (regsA n S prog)[pool[f]!.1]!
            (regsA n S prog)[pool[f]!.2]! := by
          rw [getElem!_pos cs f hf, Array.getElem_map, ← getElem!_pos pool f hf']
        rw [e, map_commutatorElement, ← permOfArr_eq_of_rep ha, ← permOfArr_eq_of_rep hc]
        exact rep_commutatorA hv1 hv2
      · exact ⟨1, 1, fun h => absurd h hf⟩
    choose H₁ H₂ hH using hcsrep
    have hzrep : ∀ f < cs.size, Rep n (commutatorA n cP.pts[i]! cs[f]!) (ρ ⁅b, ⁅H₁ f, H₂ f⁆⁆) := by
      intro f hf
      obtain ⟨hr, hv⟩ := hH f hf
      rw [map_commutatorElement, ← permOfArr_eq_of_rep hxrep, ← permOfArr_eq_of_rep hr]
      exact rep_commutatorA hxv hv
    rcases hwit : wits[i]! with _ | ⟨fs, m⟩
    ·
      rw [hwit] at hwk
      simp only [aWitOK, Bool.not_eq_true'] at hwk
      rw [isInvolA_of_rep hxrep hb1 hb2] at hwk
      exact absurd hwk (by decide)
    · rw [hwit] at hwk
      simp only [aWitOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwk
      obtain ⟨hfs, hord⟩ := hwk
      set W : C := (fs.map fun f => ⁅b, ⁅H₁ f, H₂ f⁆⁆).prod with hW
      have hprep : Rep n (prodA n (fs.map fun f => commutatorA n cP.pts[i]! cs[f]!)) (ρ W) := by
        rw [hW, map_list_prod, List.map_map]
        apply rep_prodA
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun f hf => hzrep f (hfs f hf)
      have h4 := orderOf_of_ord4A (rep_powA hprep m) hord
      refine ⟨W, ?_, ?_⟩
      · refine list_prod_mem fun z hz => ?_
        obtain ⟨f, -, rfl⟩ := List.mem_map.mp hz
        exact subset_closure ⟨H₁ f, H₂ f, rfl⟩
      · have h1 : orderOf (ρ (W ^ m)) ∣ orderOf (W ^ m) := orderOf_map_dvd ρ (W ^ m)
        rw [map_pow, h4] at h1
        exact h1.trans (orderOf_pow_dvd m)

theorem kernel_and_conj {C : Type*} [Group C] [Finite C] {n : ℕ} (ρ : C →* Perm (Fin n))
    {Q : Subgroup (Perm (Fin n))} (hQ : Q ≤ ρ.range) {k m : ℕ} (hQc : Nat.card Q = 2 ^ k)
    (hC : Nat.card C = 2 ^ (k + 1) * m) (hm : ¬ 2 ∣ m) {a : C} (ha : ρ a = 1) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) :
    ¬ 4 ∣ Nat.card ρ.ker ∧ ∀ b : C, b ^ 2 = 1 → ∃ c : C, ρ (c * b * c⁻¹) ∈ Q := by
  have hK : Nat.card ρ.ker * Nat.card ρ.range = Nat.card C := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hPc : Nat.card (Q.subgroupOf ρ.range) = 2 ^ k := by
    rw [← hQc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have hPM := (Q.subgroupOf ρ.range).card_mul_index
  have h2K : 2 ∣ Nat.card ρ.ker := by
    have : orderOf (⟨a, ha⟩ : ρ.ker) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime ha2 ha1
    rw [← this]
    exact orderOf_dvd_natCard _
  obtain ⟨j, hj⟩ := h2K
  have hjm : j * (Q.subgroupOf ρ.range).index = m := by
    have heq : 2 * j * (2 ^ k * (Q.subgroupOf ρ.range).index) = 2 ^ (k + 1) * m := by
      rw [← hj, ← hPc, hPM, hK, hC]
    have hpos : 0 < 2 ^ (k + 1) := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← heq, pow_succ]
    ring
  refine ⟨fun h4 => ?_, fun b hb => ?_⟩
  · rw [hj] at h4
    have h2j : 2 ∣ j := by omega
    exact hm (hjm ▸ dvd_mul_of_dvd_left h2j _)
  · have hidx : ¬ 2 ∣ (Q.subgroupOf ρ.range).index := fun h =>
      hm (hjm ▸ dvd_mul_of_dvd_right h _)
    have hP : IsPGroup 2 (Q.subgroupOf ρ.range) := IsPGroup.of_card hPc
    have he : (⟨ρ b, ⟨b, rfl⟩⟩ : ρ.range) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hb, map_one, OneMemClass.coe_one])
    obtain ⟨g, hg⟩ := exists_conj_mem_of_index hP hidx he
    obtain ⟨c, hc⟩ := g.2
    refine ⟨c, ?_⟩
    rw [mem_subgroupOf] at hg
    rw [map_mul, map_mul, map_inv, hc]
    simpa using hg

section Local

variable {G : Type*} [Group G] {H : Subgroup G}

theorem yWitness_of_local [Finite G] {X E : Subgroup ↥H} (hX : X.Normal) {r : ↥H} (hr1 : r ≠ 1)
    {C : Type*} [Group C] (ψ : C →* ↥H) (hψ : Function.Injective ψ)
    (hψX : ∀ c, ψ c ∈ X ⊓ centralizer {r}) (hψs : ∀ x ∈ X ⊓ centralizer {r}, ∃ c, ψ c = x)
    {n : ℕ} (ρ : C →* Perm (Fin n)) (hker : ¬ 4 ∣ Nat.card ρ.ker)
    (hconj : ∀ b : C, b ^ 2 = 1 → ρ b ≠ 1 → ∃ c : C,
      ∃ W ∈ closure {y | ∃ h₁ h₂ : C, y = ⁅c * b * c⁻¹, ⁅h₁, h₂⁆⁆}, 4 ∣ orderOf W)
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hEX : E ≤ X) (hrE : r ∈ E) :
    YWitness X E := by
  have hErange : E ≤ ψ.range := fun x hx => by
    have hxr : x ∈ centralizer {r} := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨r, hrE⟩)
    obtain ⟨c, hc⟩ := hψs x (mem_inf.mpr ⟨hEX hx, hxr⟩)
    exact ⟨c, hc⟩
  have hmap : (E.comap ψ).map ψ = E := by
    rw [map_comap_eq, inf_eq_right.mpr hErange]
  have hcard : Nat.card (E.comap ψ) = Nat.card E := by
    rw [← hmap, card_map_of_injective hψ, hmap]
  obtain ⟨b₀, hb₀E, hb₀⟩ : ∃ b₀ ∈ E.comap ψ, ρ b₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : E.comap ψ ≤ ρ.ker := fun x hx => hcon x hx
    have hdvd := card_dvd_of_le hle
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
    rw [hcard, hj] at hdvd
    have hj2 : 2 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> simp_all
    have h4 : 4 ∣ 2 ^ j := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      exact ⟨2 ^ i, by ring⟩
    exact hker (h4.trans hdvd)
  have hb₀2 : b₀ ^ 2 = 1 := hψ (by rw [map_pow, map_one]; exact hE.2 _ hb₀E)
  obtain ⟨c, W, hW, hW4⟩ := hconj b₀ hb₀2 hb₀
  have hcr : ψ c * r = r * ψ c := mem_centralizer_singleton_iff.mp (mem_inf.mp (hψX c)).2
  refine yWitness_of_root_conj hX hrE hr1 hb₀E hcr (w := ψ W) ?_ ?_
  · have h := mem_map_of_mem ψ hW
    rw [MonoidHom.map_closure] at h
    refine (closure_le _).mpr ?_ h
    rintro _ ⟨y, ⟨h₁, h₂, rfl⟩, rfl⟩
    refine subset_closure ⟨⁅ψ h₁, ψ h₂⁆, commutator_mem_commutator (hψX h₁) (hψX h₂), ?_⟩
    rw [map_commutatorElement, map_commutatorElement, map_mul, map_mul, map_inv]
  · rwa [orderOf_injective ψ hψ W]

theorem yWitness_of_aCheck [Finite G] {X E : Subgroup ↥H} (hX : X.Normal) {r : ↥H} (hr1 : r ≠ 1)
    {C : Type*} [Group C] [Finite C] (ψ : C →* ↥H) (hψ : Function.Injective ψ)
    (hψX : ∀ c, ψ c ∈ X ⊓ centralizer {r}) (hψs : ∀ x ∈ X ⊓ centralizer {r}, ∃ c, ψ c = x)
    {n : ℕ} (ρ : C →* Perm (Fin n)) {S : Array (Array ℕ)} {g : ℕ → C}
    (hS : ∀ s < S.size, Rep n S[s]! (ρ (g s))) {prog : List (ℕ × ℕ)} {pregs : List ℕ}
    {pool : Array (ℕ × ℕ)} {ps : List ℕ} {N : ℕ} {wits : Array AWit}
    (hc : aCheck n S prog pregs pool ps N wits = true) {k m : ℕ} (hN : N = 2 ^ k)
    (hC : Nat.card C = 2 ^ (k + 1) * m) (hm : ¬ 2 ∣ m) {a : C} (ha : ρ a = 1) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hEX : E ≤ X)
    (hrE : r ∈ E) : YWitness X E := by
  obtain ⟨Q, hQ, hQc, hW⟩ := aCheck_spec ρ hS hc
  obtain ⟨hker, hconj⟩ := kernel_and_conj ρ hQ (hQc.trans hN) hC hm ha ha1 ha2
  refine yWitness_of_local hX hr1 ψ hψ hψX hψs ρ hker (fun b hb2 hb1 => ?_) hE hE4 hEX hrE
  obtain ⟨c, hcQ⟩ := hconj b hb2
  have h2 : ρ (c * b * c⁻¹) * ρ (c * b * c⁻¹) = 1 := by
    rw [← map_mul, ← pow_two, conj_pow, hb2, mul_one, mul_inv_cancel, map_one]
  have h1 : ρ (c * b * c⁻¹) ≠ 1 := fun h => hb1 (by
    rw [map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
    exact h)
  obtain ⟨W, hWm, hW4⟩ := hW (c * b * c⁻¹) hcQ h2 h1
  exact ⟨c, W, hWm, hW4⟩

theorem sq_eq_one_of_val {x : ↥H} (h : (x : G) ^ 2 = 1) : x ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one])

theorem map_mem_centralizer_iff {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (g s : A) : f g ∈ centralizer {f s} ↔ g ∈ centralizer {s} := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact hf.eq_iff

end Local

noncomputable abbrev CA : Subgroup JH := centralizer {aJ}

@[expose] noncomputable def g6O
    (s : ℕ) : ↥CA := if h : s < 12 then CFSG.Sporadic.HNOddCore.g6C ⟨s, h⟩ else 1

theorem om0Gens_size : om0Gens.size = 12 := by
  simp [om0Gens, row6_parts.2.2.2.2.1]

theorem rep_g6O
    {s : ℕ} (hs : s < om0Gens.size) : Rep 1100 om0Gens[s]! (phi6 (g6O s)) := by
  have hs12 : s < 12 := by rwa [om0Gens_size] at hs
  have h := prep_phi6 ⟨s, hs12⟩
  rw [g6O, dite_eq_left hs12]
  exact h

@[expose] noncomputable def aC : ↥CA :=
  ⟨aJ, (mem_centralizer_singleton_iff (g := aJ) (k := aJ)).2 rfl⟩

theorem aC_val : (aC : JH) = aJ := rfl

theorem phi6_aC :
    phi6 aC = 1 :=
  MonoidHom.mem_ker.1 t6C_mem_ker

theorem aC_ne_one :
    aC ≠ 1 := fun h => aJ_ne_one (by
  have e := congrArg Subtype.val h
  rwa [Subgroup.coe_one, aC_val] at e)

theorem aC_sq : aC ^ 2 = 1 :=
  sq_eq_one_of_val (by rw [aC_val]; exact aJ_sq)

@[expose] noncomputable def psiA :
    ↥CA →* ↥RH := jR.comp CA.subtype

theorem psiA_apply
    (c : ↥CA) : psiA c = jR (c : JH) := rfl

theorem psiA_injective :
    Function.Injective psiA := fun a b h =>
  Subtype.ext (jR_injective (by rwa [psiA_apply, psiA_apply] at h))

theorem psiA_mem
    (c : ↥CA) : psiA c ∈ JH.subgroupOf RH ⊓ centralizer {jR aJ} := by
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_subgroupOf, psiA_apply, jR_val]
    exact (c : JH).2
  · rw [mem_centralizer_singleton_iff, psiA_apply, ← map_mul, ← map_mul]
    exact congrArg jR (comm_of_mem_centralizer c.2)

theorem exists_psiA
    {x : ↥RH} (hx : x ∈ JH.subgroupOf RH ⊓ centralizer {jR aJ}) :
    ∃ c : ↥CA, psiA c = x := by
  obtain ⟨hxX, hxC⟩ := mem_inf.mp hx
  rw [mem_subgroupOf] at hxX
  have hg : jR ⟨_, hxX⟩ = x := Subtype.ext (by rw [jR_val])
  have hgc : (⟨_, hxX⟩ : JH) ∈ CA := by
    show (⟨_, hxX⟩ : JH) ∈ centralizer {aJ}
    rw [← map_mem_centralizer_iff jR_injective, hg]
    exact hxC
  exact ⟨⟨_, hgc⟩, hg⟩

theorem jR_aJ_ne_one :
    jR aJ ≠ 1 := by
  intro h
  apply aJ_ne_one
  apply jR_injective
  rw [map_one]
  exact h

theorem yWitness_of_mem_aR
    {prog : List (ℕ × ℕ)} {pregs : List ℕ} {pool : Array (ℕ × ℕ)}
    {wits : Array AWit} (hcA : hnAOCheck prog pregs pool wits = true) {E : Subgroup ↥RH}
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hEX : E ≤ JH.subgroupOf RH)
    (ha : jR aJ ∈ E) : YWitness (JH.subgroupOf RH) E :=
  yWitness_of_aCheck normal_X jR_aJ_ne_one psiA psiA_injective psiA_mem
    (fun _ hx => exists_psiA hx) (n := 1100) phi6 (S := om0Gens) (g := g6O)
    (fun _ hs => rep_g6O hs) (by unfold hnAOCheck at hcA; exact hcA) (k := 10)
    (m := 86625) (by norm_num) (card_CJ_t6.trans (by norm_num)) (by norm_num) phi6_aC aC_ne_one
    aC_sq hE hE4 hEX ha

end CFSG.ComponentClassification.RankTwoSporadic.HN
