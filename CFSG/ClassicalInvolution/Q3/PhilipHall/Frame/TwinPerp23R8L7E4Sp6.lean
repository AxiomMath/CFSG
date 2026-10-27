module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Model
public import Certificates.Certificate507401

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

theorem exists_twin_emb
    {M : Type} [Group M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1)
    {K : Subgroup M} {s : M} (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x)
    {y : M} (hne : conjSub y K ≠ K) (hle : conjSub y K ≤ Subgroup.normalizer (K : Set M)) :
    ∃ φ : M →* Equiv.Perm (Fin 36), Function.Injective φ ∧ φ.range = co3X36 ∧ φ s = sp6Rep2 ∧
      K.map φ = K0 ∧ (conjSub y K).map φ = conjSub (twin ()) K0 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKφ⟩ := TwinThmE.exists_emb_of_ident e
    (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  have hs : φ s = sp6Rep2 :=
    E4Sp6.eq_rep_of_isUniqueInvolution (hKφ ▸ Vtx.isUniqueInvolution_map φ hφ hinv)
  have hK'φ : (conjSub y K).map φ = conjSub (φ y) K0 := by
    rw [AscQuot.map_conjSub, hKφ]
  have hBK : conjSub (φ y) K0 = conjSub (twin ()) K0 := by
    refine E4Sp6.eq_twin_of_le_normalizer (hmem y) (fun h1 => hne ?_) ?_
    · apply Subgroup.map_injective hφ
      rw [hK'φ, h1, hKφ]
    · rw [← hK'φ, ← hKφ]
      exact (Vtx.map_le_normalizer_map_iff φ hφ).mpr hle
  exact ⟨φ, hφ, hrange, hs, hKφ, hK'φ.trans hBK⟩

theorem mem_enumeration_of_comm
    {x : Equiv.Perm (Fin 36)} (hx : x ∈ co3X36)
    (hxr : x * sp6Rep2 = sp6Rep2 * x) : x ∈ enumeration sp6CentQ2 := by
  have hQv := (E4Sp6.cover_of_centCheck (by rw [sp6CentQ2, certificate_originalSubgroup])
    exists_word_of_mem_map sp6_cent_check₂).1
  rw [mem_enumeration_iff _ hQv, ← sp6_cent_spec₂.1, sp6Q_originalSubgroup]
  exact mem_centralizerIn.2 ⟨hx, hxr⟩

theorem mem_memberElems_iff (w x : Equiv.Perm (Fin 36)) :
    x ∈ memberElems (L0 ()) w ↔ x ∈ conjSub w K0 := by
  rw [mem_conjSub_iff, E4Sp6.mem_K0_iff, memberElems, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [tab_eq, show w⁻¹ * (w * q * w⁻¹) * w = q by group]
    exact hq
  · intro hx
    exact ⟨w⁻¹ * x * w, hx, by rw [tab_eq]; group⟩

theorem mem_L1_iff (x : Equiv.Perm (Fin 36)) :
    x ∈ L1 () ↔ x ∈ conjSub (twin ()) K0 := by
  rw [mem_conjSub_iff, E4Sp6.mem_K0_iff, L1, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [show (twin ())⁻¹ * (twin () * q * (twin ())⁻¹) * twin () = q by group]
  · intro hx
    exact ⟨_, hx, by group⟩

theorem commAll_of_le_centralizer {M : Type} [Group M] (φ : M →* Equiv.Perm (Fin 36))
    {L : Subgroup M} {g : M} (hg : L ≤ Subgroup.centralizer ({g} : Set M))
    {l : List (Equiv.Perm (Fin 36))} (hl : ∀ x ∈ l, x ∈ L.map φ) : commAll (φ g) l = true := by
  simp only [commAll, List.all_eq_true, decide_eq_true_eq]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := hl x hx
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hg hk)]

theorem le_centralizer_of_commAll {M : Type} [Group M] {φ : M →* Equiv.Perm (Fin 36)}
    (hφ : Function.Injective φ) {J : Subgroup M} {g : M} {l : List (Equiv.Perm (Fin 36))}
    (hJ : ∀ x ∈ J.map φ, x ∈ l) (h : commAll (φ g) l = true) :
    J ≤ Subgroup.centralizer ({g} : Set M) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := List.all_eq_true.1 h (φ x) (hJ _ (Subgroup.mem_map_of_mem φ hx))
  simp only [decide_eq_true_eq] at h1
  apply hφ
  rw [map_mul, map_mul]
  exact h1.symm

def IsLay (c : Equiv.Perm (Fin 36)) : Prop :=
  c ∈ enumeration sp6CentQ2 ∧ commAll c (L0 ()) = true ∧ commAll c (L1 ()) = true ∧ c ≠ 1 ∧
    ¬ ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
      ¬ commAll c (memberElems (L0 ()) ((ws ()).getD k 1)) = true

theorem twinLay_parts {a b : Equiv.Perm (Fin 36)}
    (ha : IsLay a) (hb : IsLay b) (hab : a ≠ b) :
    ∃ k < (ws ()).length, commAll a (memberElems (L0 ()) ((ws ()).getD k 1)) = true ∧
      ∃ z ∈ memberElems (L0 ()) ((ws ()).getD k 1), ordThree (z * b * z⁻¹ * b⁻¹) = true := by
  have h := Certificates.certificate507401
  simp only [twinLayCheck, List.all_eq_true, List.mem_filter, List.mem_map, Bool.and_eq_true,
    Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_true_eq] at h
  have conv : ∀ c, IsLay c → ((∃ a ∈ enumeration sp6CentQ2, tab a = c) ∧ commAll c (L0 ()) = true ∧
      commAll c (L1 ()) = true) ∧ decide (c = 1) = false ∧
      ((List.range (ws ()).length).all fun k =>
        k == 0 || k == 11 || !commAll c (memberElems (L0 ()) ((ws ()).getD k 1))) = false := by
    rintro c ⟨hQ, hL0, hL1, h1, hw⟩
    refine ⟨⟨⟨c, hQ, tab_eq c⟩, hL0, hL1⟩, decide_eq_false h1, ?_⟩
    rw [Bool.eq_false_iff]
    intro hall
    apply hw
    intro k hk
    have := List.all_eq_true.1 hall k (List.mem_range.2 hk)
    simpa only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_true, or_assoc] using this
  exact (h a (conv a ha) b (conv b hb)).resolve_left hab

theorem Ea_le_sup
    {M : Type} [Group M]
    {K : Subgroup M} {y : M} {φ : M →* Equiv.Perm (Fin 36)} (hφ : Function.Injective φ)
    (hmem : ∀ m, φ m ∈ co3X36) (hKφ : K.map φ = K0)
    (hK'φ : (conjSub y K).map φ = conjSub (twin ()) K0) {c : M}
    (h : ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
      ¬ commAll (φ c) (memberElems (L0 ()) ((ws ()).getD k 1)) = true) :
    Ea (CoreAssembly.conjClass K) c ≤ K ⊔ conjSub y K := by
  refine Ea_le fun J hJ hJc => ?_
  obtain ⟨m, rfl⟩ := hJ
  beta_reduce at hJc ⊢
  have hJφ : (conjSub m K).map φ = conjSub (φ m) K0 := by rw [AscQuot.map_conjSub, hKφ]
  obtain ⟨k, hk, hek⟩ := E4Sp6.exists_member (hmem m)
  have hcomm : commAll (φ c) (memberElems (L0 ()) ((ws ()).getD k 1)) = true :=
    commAll_of_le_centralizer φ hJc fun x hx => by
      rw [hJφ, hek]
      exact (mem_memberElems_iff _ x).1 hx
  rcases h k hk with rfl | rfl | hnc
  · have : conjSub m K = K := by
      apply Subgroup.map_injective hφ
      rw [hJφ, hek, E4Sp6.ws_zero, conjSub_one, hKφ]
    rw [this]
    exact le_sup_left
  · have : conjSub m K = conjSub y K := by
      apply Subgroup.map_injective hφ
      rw [hJφ, hek, hK'φ]
      rfl
    rw [this]
    exact le_sup_right
  · exact absurd hcomm hnc

theorem isSolvable_Ea
    {M : Type} [Group M] [Finite M]
    {K : Subgroup M} {y : M} {φ : M →* Equiv.Perm (Fin 36)} (hφ : Function.Injective φ)
    (hmem : ∀ m, φ m ∈ co3X36) (hKφ : K.map φ = K0)
    (hK'φ : (conjSub y K).map φ = conjSub (twin ()) K0) (hK2 : IsPGroup 2 ↥K)
    (hle : conjSub y K ≤ Subgroup.normalizer (K : Set M)) {c : M}
    (h : ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
      ¬ commAll (φ c) (memberElems (L0 ()) ((ws ()).getD k 1)) = true) :
    Group.IsSolvable ↥(Ea (CoreAssembly.conjClass K) c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2' : IsPGroup 2 ↥(conjSub y K) := Vtx.isPGroup_of_mem_conjClass hK2 ⟨y, rfl⟩
  have hP : IsPGroup 2 ↥(Ea (CoreAssembly.conjClass K) c) :=
    (hK2.to_sup_of_normal_left' hK2' hle).to_le (Ea_le_sup hφ hmem hKφ hK'φ h)
  have : Group.IsNilpotent ↥(Ea (CoreAssembly.conjClass K) c) := hP.isNilpotent
  infer_instance

theorem e4TwinLayW_sp6
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4TwinLayW M := by
  intro K K' s hq hinv htw hK' hne hle _ a b ha1 hb1 hab haK haK' hbK hbK' hna hnb
  obtain ⟨y, rfl⟩ := hK'
  obtain ⟨φ, hφ, hrange, hs, hKφ, hK'φ⟩ := exists_twin_emb hM hq hinv htw hne hle
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  obtain ⟨eK⟩ := hq
  have hK2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num)
  have hlay : ∀ c : M, c ≠ 1 → K ≤ Subgroup.centralizer ({c} : Set M) →
      conjSub y K ≤ Subgroup.centralizer ({c} : Set M) →
      ¬ Group.IsSolvable ↥(Ea (CoreAssembly.conjClass K) c) → IsLay (φ c) := by
    intro c hc1 hcK hcK' hnc
    refine ⟨?_, commAll_of_le_centralizer φ hcK fun x hx => ?_,
      commAll_of_le_centralizer φ hcK' fun x hx => ?_, fun h1 => hc1 (hφ (by rw [h1, map_one])),
      fun h => hnc (isSolvable_Ea hφ hmem hKφ hK'φ hK2 hle h)⟩
    · refine mem_enumeration_of_comm (hmem c) ?_
      rw [← hs, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hcK hinv.mem)]
    · rw [hKφ]
      exact (E4Sp6.mem_K0_iff x).2 hx
    · rw [hK'φ]
      exact (mem_L1_iff x).1 hx
  obtain ⟨k, -, hak, z, hz, hzb⟩ :=
    twinLay_parts (hlay a ha1 haK haK' hna) (hlay b hb1 hbK hbK' hnb) fun h => hab (hφ h)
  obtain ⟨m, hm⟩ : ∃ m, φ m = (ws ()).getD k 1 := by
    have := E4Sp6.ws_mem k
    rw [← hrange] at this
    exact this
  have hJφ : (conjSub m K).map φ = conjSub ((ws ()).getD k 1) K0 := by
    rw [AscQuot.map_conjSub, hKφ, hm]
  have hJa : conjSub m K ≤ Subgroup.centralizer ({a} : Set M) :=
    le_centralizer_of_commAll hφ (fun x hx => (mem_memberElems_iff _ x).2 (by rwa [hJφ] at hx)) hak
  have hz' : z ∈ (conjSub m K).map φ := by
    rw [hJφ]
    exact (mem_memberElems_iff _ z).1 hz
  obtain ⟨x, hxJ, rfl⟩ := hz'
  simp only [ordThree, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hzb
  obtain ⟨hz1, hz3⟩ := hzb
  have hc : φ (x * b * x⁻¹ * b⁻¹) = φ x * φ b * (φ x)⁻¹ * (φ b)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hJmem : conjSub m K ∈ CoreAssembly.conjClass K := ⟨m, rfl⟩
  refine ⟨x, le_Ea hJmem hJa hxJ, fun h1 => hz1 ?_, hφ ?_⟩
  · rw [← hc, h1, map_one]
  · rw [map_pow, hc, map_one, pow_three']
    exact hz3

theorem e4TwinLayModel_of_certs :
    E4TwinLayModel := by
  intro M _ _ hM
  rcases hM with hM | hM
  · exact e4TwinLayW_sp6 hM
  · intro K K' s hq hinv htw _ _ _ hperp
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁K, hJ₂K, hJ₁₂, hn₁, hn₂⟩ :=
      TwinDisc.e4O8TwinModel_of_certs M hM K s hq hinv htw
    exact absurd ((hperp J₁ hJ₁ hJ₁K hn₁).trans (hperp J₂ hJ₂ hJ₂K hn₂).symm) hJ₁₂

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
