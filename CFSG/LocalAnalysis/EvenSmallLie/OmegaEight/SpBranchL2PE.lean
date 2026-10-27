module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

theorem chiV_zero_left (n v : ℕ) : chiV n 0 v = false := by
  have : chiV n 0 v = chiV n 0 0 := by unfold chiV; simp [Nat.and_zero]
  rw [this, chiV_zero]

variable {G : Type*} [Group G] {S : Subgroup G} (e : S ≃* SModel)

theorem pEps_of {t : G} (htS : t ∈ S) {i : ℕ} (hti : (e ⟨t, htS⟩).code = l2T.getD i 0)
    {gs : List ℕ} {ps : List (ℕ × ℕ)} (hk : l2THOK i gs ps = true) :
    Nat.card (S ⊓ centralizer ({t} : Set G) : Subgroup G) = 16384 ∧
      ∀ K : Subgroup G, K ≤ S ⊓ centralizer ({t} : Set G) →
        K.relIndex (S ⊓ centralizer ({t} : Set G)) = 2 → t ∈ K →
          (nInv K, nOrd4 K) ∈ l2PLit.getD i [] := by
  classical
  set Φ := sIso e
  set P := S ⊓ centralizer ({t} : Set G)
  have hfS : Finite S := (sIso e).finite
  have hfG : ∀ c, c < 65536 → (elt Φ c : G) ∈ S := fun c _ => (Φ.g c).2
  set tc := l2T.getD i 0
  have htc : Φ.f ⟨t, htS⟩ = tc := hti
  set L := dblL sMul gs ps with hLdef
  unfold l2THOK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    List.mem_range, ← hLdef] at hk
  obtain ⟨⟨⟨⟨⟨⟨hgl, hgs⟩, hps⟩, hnd⟩, hlen⟩, hall⟩, hmask⟩ := hk
  have hnd' := nodup_of_nodupM hnd
  have hcomm : ∀ c, c < 65536 → ((elt Φ c : G) * t = t * elt Φ c ↔ sMul c tc = sMul tc c) := by
    intro c hc
    have ht' : (t : G) = ((⟨t, htS⟩ : S) : G) := rfl
    rw [ht', ← htc, ← Φ.f_g hc, ← Φ.map_mul, ← Φ.map_mul, Φ.f_eq_iff, Φ.f_g hc]
    unfold elt
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have hmemP : ∀ c, c < 65536 → sMul c tc = sMul tc c → elt Φ c ∈ P := fun c hc h =>
    ⟨hfG c hc, mem_centralizer_singleton_iff.2 ((hcomm c hc).2 h)⟩
  have hgP : ∀ g ∈ gs, elt Φ g ∈ P := fun g hg => hmemP g (hgs g hg).1 (hgs g hg).2
  have hps' : ∀ st ∈ ps, st.2 < gs.length ∨ (st.1 < 65536 ∧ elt Φ st.1 ∈ P) := by
    intro st hst
    rcases hps st hst with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, hmemP _ h.1 h.2⟩
  have hD := dbl_props Φ sMul_zero_zero (fun g hg => (hgs g hg).1) hgP hps' (fun _ => false)
    (fun _ _ _ _ => rfl) (n := 5) (b := 0) hgl fun k _ => by rw [Nat.zero_testBit]
  rw [← hLdef] at hD
  have hLs : ∀ x ∈ L, x.1 < 65536 ∧ sMul x.1 tc = sMul tc x.1 := by
    intro x hx
    obtain ⟨hlt, hP, -⟩ := hD x hx
    refine ⟨hlt, (hcomm _ hlt).1 ?_⟩
    exact mem_centralizer_singleton_iff.1 hP.2
  have hcardP : Nat.card P = 16384 := by
    have h1 := card_comm Φ ⟨t, htS⟩
    rw [htc, hall] at h1
    rw [h1]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_centralizer_singleton_iff.1 x.2.2))⟩
        invFun := fun y => ⟨y.1, y.1.2, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  refine ⟨hcardP, fun K hKP hK htK => ?_⟩
  obtain ⟨b, hb, hmemL, hI, hO⟩ := counts_of_index_two Φ sMul_zero_zero hLdef
    (fun g hg => (hgs g hg).1) hgP hps' hnd' (by rw [hcardP, hlen]) inf_le_left hgl hKP hK
  have htlt : tc < 65536 := by rw [← htc]; exact Φ.lt _
  have htL : tc ∈ L.map Prod.fst := by
    set A := (L.map Prod.fst).toFinset
    set B := ((List.range 65536).filter fun c => sMul c tc == sMul tc c).toFinset
    have hAB : A ⊆ B := by
      intro c hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
      exact List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (hLs x hx).1,
        beq_iff_eq.2 (hLs x hx).2⟩)
    have hcA : A.card = 16384 := by
      rw [List.toFinset_card_of_nodup hnd', List.length_map, hlen]
    have hcB : B.card = 16384 := by
      rw [List.toFinset_card_of_nodup ((List.nodup_range).filter _), hall]
    have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hcA, hcB])
    have : tc ∈ B := List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 htlt, by simp⟩)
    rw [← heq] at this
    exact List.mem_toFinset.1 this
  obtain ⟨x, hxL, hxt⟩ := List.mem_map.1 htL
  have hvec : vecOf L tc = x.2.2.2 := by
    unfold vecOf
    obtain ⟨y, hy, hyc⟩ : ∃ y, L.find? (fun e => e.1 == tc) = some y ∧ y.1 = tc := by
      have hs : (L.find? fun e => e.1 == tc).isSome :=
        List.find?_isSome.2 ⟨x, hxL, by rw [hxt, beq_self_eq_true]⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
      have := List.find?_some hy
      exact ⟨y, hy, beq_iff_eq.1 this⟩
    have hyx : y = x := List.inj_on_of_nodup_map hnd' (List.mem_of_find?_eq_some hy) hxL
      (by rw [hyc, hxt])
    rw [hy, Option.map_some, Option.getD_some, hyx]
  have htx : elt Φ x.1 = t := by
    rw [hxt, ← htc]; unfold elt; rw [Φ.g_f]
  have htK' : chiV 5 b x.2.2.2 = false := by
    have := (hmemL x hxL).1
    rw [htx] at this
    exact this htK
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hle : P ≤ K := by
      intro z hz
      have hzS : z ∈ S := hz.1
      have hzc : Φ.f ⟨z, hzS⟩ ∈ L.map Prod.fst := by
        set A := (L.map Prod.fst).toFinset
        set B := ((List.range 65536).filter fun c => sMul c tc == sMul tc c).toFinset
        have hAB : A ⊆ B := by
          intro c hc
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
          exact List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (hLs x hx).1,
            beq_iff_eq.2 (hLs x hx).2⟩)
        have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by
          rw [List.toFinset_card_of_nodup hnd', List.length_map, hlen,
            List.toFinset_card_of_nodup ((List.nodup_range).filter _), hall])
        have hzB : Φ.f ⟨z, hzS⟩ ∈ B := by
          refine List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 (Φ.lt _), ?_⟩)
          rw [beq_iff_eq]
          have h1 := (hcomm _ (Φ.lt ⟨z, hzS⟩)).1
          apply h1
          unfold elt
          rw [Φ.g_f]
          exact mem_centralizer_singleton_iff.1 hz.2
        rw [← heq] at hzB
        exact List.mem_toFinset.1 hzB
      obtain ⟨w, hwL, hwz⟩ := List.mem_map.1 hzc
      have := (hmemL w hwL).2 (chiV_zero_left 5 _)
      have hzw : elt Φ w.1 = z := by rw [hwz]; unfold elt; rw [Φ.g_f]
      rwa [hzw] at this
    have : K.relIndex P = 1 := relIndex_eq_one.2 hle
    omega
  have hb32 : b < 32 := lt_of_lt_of_le hb (by
    calc 2 ^ gs.length ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hgl
      _ = 32 := by norm_num)
  have hm := hmask b hb32
  rw [hvec, htK'] at hm
  simp only [Bool.or_eq_true, beq_iff_eq, hb0, Bool.false_eq_true, false_or,
    List.contains_iff_mem] at hm
  rw [hI, hO]
  exact hm

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
