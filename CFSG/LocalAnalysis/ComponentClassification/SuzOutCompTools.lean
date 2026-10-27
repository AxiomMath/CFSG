module

public import CFSG.Sporadic.SuzOddCore.CompQuot
public import CFSG.Quasithin.Recognition.CertPermSimple

public section

namespace CFSG.ComponentClassification.SuzOutComp

open CFSG CFSG.LocalCores Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Quasithin

theorem range_eq_closure_of_gens {N H : Type*} [Group N] [Group H] {E : Subgroup N} {n₀ : ℕ}
    {gen : ℕ → N} (hE : E = closure {g | ∃ k < n₀, gen k = g}) (hmem : ∀ k < n₀, gen k ∈ E)
    (ρ : E →* H) {img : ℕ → H} (himg : ∀ k (hk : k < n₀), ρ ⟨gen k, hmem k hk⟩ = img k) :
    ρ.range = closure {g | ∃ k < n₀, img k = g} := by
  have htop : (⊤ : Subgroup E) = closure (((↑) : E → N) ⁻¹' {g | ∃ k < n₀, gen k = g}) := by
    have := Subgroup.closure_closure_coe_preimage (k := {g | ∃ k < n₀, gen k = g})
    rw [← hE] at this
    exact this.symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext σ
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, ⟨k, hk, hkg⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    rw [← himg k hk]
    congr 1
    exact Subtype.ext hkg
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨gen k, hmem k hk⟩, ⟨k, hk, rfl⟩, himg k hk⟩

theorem permOfArr_wordA_mem {m : ℕ} {G : Array (Array ℕ)}
    (hG : ∀ k < G.size, isInvA m G[k]! (invCand m G[k]!) = true) {w : List ℤ}
    (hw : lettersOK G.size w = true)
    (hinv : isInvA m (wordA m G (rawInvs m G) w) (invCand m (wordA m G (rawInvs m G) w)) = true) :
    permOfArr m (wordA m G (rawInvs m G) w) ∈
      closure {g | ∃ k < G.size, permOfArr m G[k]! = g} := by
  have hG' : ∀ k < G.size, isInvA m G[k]! (rawInvs m G)[k]! = true := fun k hk => by
    rw [rawInvs_getElem! hk]
    exact hG k hk
  obtain ⟨g, hgK, hg⟩ := wordA_mem' (K := closure {g | ∃ k < G.size, permOfArr m G[k]! = g})
    (m := G.size) (fun _ => True) (fun k hk => (rep_permOfArr (hG' k hk)).1)
    (fun k hk => (rep_permOfArr (hG' k hk)).2) (fun k hk _ => subset_closure ⟨k, hk, rfl⟩) w hw
    (fun _ _ => trivial)
  rw [(rep_permOfArr hinv).1.unique hg]
  exact hgK

theorem card_quotient_center_of_injective {E X : Type*} [Group E] [Finite E] [Group X]
    (ρ : E →* X) (hinj : Function.Injective ρ) (D : Subgroup X) (hDs : IsSimpleGroup D)
    (hD : D ≤ ρ.range) (h2 : 2 * Nat.card D = Nat.card E) (hnc : ∃ a b : D, a * b ≠ b * a)
    {B : Subgroup E} (hB : IsComponent B) : Nat.card (B ⧸ center B) = Nat.card D := by
  have hker : ρ.rangeRestrict.ker = ⊥ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (MonoidHom.ker_eq_bot_iff ρ).2 hinj
  have hsol : Group.IsSolvable ρ.rangeRestrict.ker := by
    rw [hker]
    infer_instance
  set D' := D.subgroupOf ρ.range with hD'
  have e : D' ≃* D := Subgroup.subgroupOfEquivOfLe hD
  have hcardD' : Nat.card D' = Nat.card D := Nat.card_congr e.toEquiv
  have hcardR : Nat.card ρ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : D'.index = 2 := by
    have h := D'.card_mul_index
    rw [hcardD', hcardR, ← h2] at h
    have hE : 0 < Nat.card E := Nat.card_pos
    have hpos : 0 < Nat.card D := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h, mul_comm])
  have hD's : IsSimpleGroup D' := e.isSimpleGroup
  have hnc' : ∃ a b : D', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  rw [← hcardD']
  exact CFSG.Sporadic.SuzOddCore.card_quotient_center_of_component ρ.rangeRestrict
    ρ.rangeRestrict_surjective hsol D' hidx hD's hnc' hB

end CFSG.ComponentClassification.SuzOutComp
