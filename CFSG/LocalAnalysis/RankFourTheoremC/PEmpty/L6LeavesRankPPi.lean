module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCover

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

@[expose] def zhat {G : Type*} [Group G] (f : ℕ) (F : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ F ∧ (∀ s ∈ F, s * z = z * s) ∧ z ^ f = 1}
  one_mem' := ⟨F.one_mem, fun s _ => by simp, one_pow f⟩
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨haF, hac, haf⟩ := ha
    obtain ⟨hbF, hbc, hbf⟩ := hb
    refine ⟨F.mul_mem haF hbF, fun s hs => ?_, ?_⟩
    · rw [← mul_assoc, hac s hs, mul_assoc, hbc s hs, mul_assoc]
    · have hab : a * b = b * a := (hac b hbF).symm
      rw [(Commute.mul_pow hab f), haf, hbf, one_mul]
  inv_mem' := fun {a} ha => by
    obtain ⟨haF, hac, haf⟩ := ha
    refine ⟨F.inv_mem haF, fun s hs => ?_, ?_⟩
    · have := hac s hs
      calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
        _ = a⁻¹ * (s * a) * a⁻¹ := by rw [this]
        _ = a⁻¹ * s := by group
    · rw [inv_pow, haf, inv_one]

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ i, Group (C i)]
  [∀ i, Finite (C i)] {f : ℕ}

theorem isPGroup_of_map_eval (U : Subgroup (∀ i, C i))
    (hU : ∀ i, IsPGroup f (U.map (Pi.evalMonoidHom C i))) : IsPGroup f U := by
  intro x
  have hk : ∀ i, ∃ k : ℕ, ((x.1 i : C i)) ^ (f ^ k) = 1 := fun i => by
    obtain ⟨k, hk⟩ := hU i ⟨x.1 i, ⟨x.1, x.2, rfl⟩⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  choose k hk using hk
  refine ⟨∑ i, k i, Subtype.ext (funext fun i => ?_)⟩
  have hle : k i ≤ ∑ j, k j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  have : (x.1 i) ^ (f ^ (∑ j, k j)) = 1 := by
    rw [show f ^ (∑ j, k j) = f ^ k i * f ^ ((∑ j, k j) - k i) by
      rw [← pow_add]; congr 1; omega, pow_mul, hk i, one_pow]
  simpa using this

variable [Fact f.Prime]

theorem exists_pi_sylow (F : Subgroup (∀ i, C i)) (hFp : IsPGroup f F)
    (hFmax : ∀ Q : Subgroup (∀ i, C i), IsPGroup f Q → F ≤ Q → Q = F) :
    (∀ i, IsPGroup f (F.map (Pi.evalMonoidHom C i))) ∧
    (F = Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i)) ∧
    ∀ i, ∀ Q : Subgroup (C i), IsPGroup f Q → F.map (Pi.evalMonoidHom C i) ≤ Q →
      Q = F.map (Pi.evalMonoidHom C i) := by
  have hFi : ∀ i, IsPGroup f (F.map (Pi.evalMonoidHom C i)) := fun i => hFp.map _
  have hFle : F ≤ Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i) := fun x hx =>
    (Subgroup.mem_pi Set.univ).mpr fun i _ => ⟨x, hx, rfl⟩
  have hpi : IsPGroup f (Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i)) := by
    apply isPGroup_of_map_eval
    intro i
    refine (hFi i).to_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_pi Set.univ).mp hx i (Set.mem_univ i)
  have hFeq : F = Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i) :=
    (hFmax _ hpi hFle).symm
  refine ⟨hFi, hFeq, fun i Q hQ hFQ => ?_⟩
  let U' : Subgroup (∀ j, C j) :=
    Subgroup.pi {j | j ≠ i} (fun j => F.map (Pi.evalMonoidHom C j)) ⊓
      Q.comap (Pi.evalMonoidHom C i)
  have hU'p : IsPGroup f U' := by
    apply isPGroup_of_map_eval
    intro j
    by_cases h : j = i
    · subst h
      refine hQ.to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · refine (hFi j).to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_pi _).mp hx.1 j h
  have hFle' : F ≤ U' := fun x hx =>
    ⟨(Subgroup.mem_pi _).mpr fun j _ => ⟨x, hx, rfl⟩, hFQ ⟨x, hx, rfl⟩⟩
  have hU'F : U' = F := hFmax _ hU'p hFle'
  apply le_antisymm
  · intro q hq
    have hmem : (Pi.mulSingle i q : ∀ j, C j) ∈ U' := by
      refine ⟨(Subgroup.mem_pi _).mpr fun j hj => ?_, ?_⟩
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
      · show (Pi.mulSingle i q : ∀ j, C j) i ∈ Q
        rw [Pi.mulSingle_eq_same]
        exact hq
    rw [hU'F] at hmem
    exact ⟨_, hmem, by simp⟩
  · exact hFQ

theorem pi_zhat_central (F : Subgroup (∀ i, C i)) (hFp : IsPGroup f F)
    (hFmax : ∀ Q : Subgroup (∀ i, C i), IsPGroup f Q → F ≤ Q → Q = F) {z : ∀ i, C i}
    (hz : z ∈ zhat f F) (i : ι) :
    ∃ S : Sylow f (C i), z i ∈ (S : Subgroup (C i)) ∧
      ∀ s ∈ (S : Subgroup (C i)), z i * s = s * z i := by
  obtain ⟨hFi, hFeq, hFi'⟩ := exists_pi_sylow F hFp hFmax
  let S : Sylow f (C i) := ⟨F.map (Pi.evalMonoidHom C i), hFi i, fun {Q} hQ hle => hFi' i Q hQ hle⟩
  refine ⟨S, ⟨z, hz.1, rfl⟩, fun s hs => ?_⟩
  have hmem : (Pi.mulSingle i s : ∀ j, C j) ∈ F := by
    rw [hFeq]
    refine (Subgroup.mem_pi Set.univ).mpr fun j _ => ?_
    by_cases h : j = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hs
    · simp only [Pi.mulSingle_eq_of_ne h]
      exact Subgroup.one_mem _
  have := hz.2.1 _ hmem
  have h2 := congrFun this i
  simpa using h2.symm

theorem pow_le_card_zhat (F : Subgroup (∀ i, C i)) (hFp : IsPGroup f F)
    (hFmax : ∀ Q : Subgroup (∀ i, C i), IsPGroup f Q → F ≤ Q → Q = F)
    (hdvd : ∀ i, f ∣ Nat.card (C i)) : f ^ Fintype.card ι ≤ Nat.card (zhat f F) := by
  obtain ⟨hFi, hFeq, hFi'⟩ := exists_pi_sylow F hFp hFmax
  have hex : ∀ i, ∃ u : C i, u ∈ F.map (Pi.evalMonoidHom C i) ∧
      (∀ s ∈ F.map (Pi.evalMonoidHom C i), s * u = u * s) ∧ u ^ f = 1 ∧ u ≠ 1 := by
    intro i
    let S : Sylow f (C i) :=
      ⟨F.map (Pi.evalMonoidHom C i), hFi i, fun {Q} hQ hle => hFi' i Q hQ hle⟩
    have hcard : Nat.card S = f ^ (Nat.card (C i)).factorization f := Sylow.card_eq_multiplicity S
    have hpos : 0 < (Nat.card (C i)).factorization f :=
      (Fact.out : f.Prime).factorization_pos_of_dvd Nat.card_pos.ne' (hdvd i)
    have hnt : Nontrivial (S : Subgroup (C i)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      exact Nat.one_lt_pow hpos.ne' (Fact.out : f.Prime).one_lt
    obtain ⟨w, -, hwZ, hwf, hw1⟩ := exists_ne_one_mem_inf_center (p := f) S.isPGroup'
      (⊤ : Subgroup (S : Subgroup (C i))) top_ne_bot
    refine ⟨(w : C i), w.2, fun s hs => ?_, ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp hwZ ⟨s, hs⟩
      exact (congrArg Subtype.val this)
    · simpa using congrArg Subtype.val hwf
    · intro h
      exact hw1 (Subtype.ext h)
  choose u hu1 hu2 hu3 hu4 using hex
  have hψ : ∀ a : ι → Fin f, (fun j => (u j) ^ (a j : ℕ)) ∈ zhat f F := by
    intro a
    refine ⟨?_, ?_, ?_⟩
    · rw [hFeq]
      exact (Subgroup.mem_pi Set.univ).mpr fun j _ => Subgroup.pow_mem _ (hu1 j) _
    · intro s hs
      funext j
      have hsj : s j ∈ F.map (Pi.evalMonoidHom C j) := ⟨s, hs, rfl⟩
      have hc : Commute (s j) (u j) := hu2 j (s j) hsj
      exact (hc.pow_right (a j : ℕ)).eq
    · funext j
      show ((u j) ^ (a j : ℕ)) ^ f = 1
      rw [← pow_mul, mul_comm, pow_mul, hu3 j, one_pow]
  let ψ : (ι → Fin f) → zhat f F := fun a => ⟨fun j => (u j) ^ (a j : ℕ), hψ a⟩
  have hinj : Function.Injective ψ := by
    intro a b hab
    funext j
    have h1 : (u j) ^ (a j : ℕ) = (u j) ^ (b j : ℕ) := congrFun (congrArg Subtype.val hab) j
    have hord : orderOf (u j) = f := orderOf_eq_prime (hu3 j) (hu4 j)
    have := pow_injOn_Iio_orderOf (x := u j) (by rw [hord]; exact (a j).2)
      (by rw [hord]; exact (b j).2) h1
    exact Fin.ext this
  calc f ^ Fintype.card ι = Nat.card (ι → Fin f) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card]
    _ ≤ Nat.card (zhat f F) := Nat.card_le_card_of_injective ψ hinj

theorem zhat_equiv {G : Type*} [Group G] [Finite G] (e : G ≃* (∀ i, C i)) (F : Subgroup G)
    (hFp : IsPGroup f F) (hFmax : ∀ Q : Subgroup G, IsPGroup f Q → F ≤ Q → Q = F)
    (hdvd : ∀ i, f ∣ Nat.card (C i)) :
    (∀ z ∈ zhat f F, ∀ i, ∃ S : Sylow f (C i), e z i ∈ (S : Subgroup (C i)) ∧
      ∀ s ∈ (S : Subgroup (C i)), e z i * s = s * e z i) ∧
    f ^ Fintype.card ι ≤ Nat.card (zhat f F) := by
  let F' : Subgroup (∀ i, C i) := F.map e.toMonoidHom
  have hF'p : IsPGroup f F' := hFp.map _
  have hF'max : ∀ Q : Subgroup (∀ i, C i), IsPGroup f Q → F' ≤ Q → Q = F' := by
    intro Q hQ hle
    have h1 : IsPGroup f (Q.comap e.toMonoidHom) :=
      hQ.comap_of_injective _ e.injective
    have h2 : F ≤ Q.comap e.toMonoidHom := fun x hx => hle ⟨x, hx, rfl⟩
    have h3 := hFmax _ h1 h2
    apply le_antisymm
    · intro q hq
      obtain ⟨x, hx⟩ := e.surjective q
      have hxq : x ∈ Q.comap e.toMonoidHom := by
        show e x ∈ Q
        rw [hx]
        exact hq
      rw [h3] at hxq
      exact ⟨x, hxq, hx⟩
    · exact hle
  have hmem : ∀ z : G, z ∈ zhat f F → e z ∈ zhat f F' := fun z hz =>
    ⟨⟨z, hz.1, rfl⟩, fun w ⟨s, hs, hse⟩ => by
      rw [← hse]
      show e s * e z = e z * e s
      rw [← map_mul, ← map_mul, hz.2.1 s hs],
      by rw [← map_pow, hz.2.2, map_one]⟩
  refine ⟨fun z hz i => pi_zhat_central F' hF'p hF'max (hmem z hz) i, ?_⟩
  calc f ^ Fintype.card ι ≤ Nat.card (zhat f F') := pow_le_card_zhat F' hF'p hF'max hdvd
    _ ≤ Nat.card (zhat f F) := by
        have : Function.Surjective (fun z : zhat f F => (⟨e z, hmem z z.2⟩ : zhat f F')) := by
          rintro ⟨w, hw⟩
          obtain ⟨z, hz⟩ := e.surjective w
          refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
          obtain ⟨⟨x, hx, hxe⟩, hc, hf⟩ := hw
          subst hz
          have hxz : x = z := e.injective hxe
          refine ⟨hxz ▸ hx, fun s hs => ?_, ?_⟩
          · have := hc (e s) ⟨s, hs, rfl⟩
            apply e.injective
            rw [map_mul, map_mul]
            exact this
          · apply e.injective
            rw [map_pow, hf, map_one]
        exact Nat.card_le_card_of_surjective _ this

end Pi

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
