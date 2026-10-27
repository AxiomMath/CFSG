module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable
  {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem gomi_card_fixedRootSpan_thetaOrbit {α : Fin τ.rank → ℤ} (hα : α ∈ D.roots) :
    Nat.card ↥(D.fixedRootSpan (thetaOrbit D.θ α)) = D.q ^ (thetaOrbit D.θ α).ncard := by
  obtain ⟨hO, hlift, hspec, hex, hiso, -⟩ := orthogonal_fixed_orbit_rank_one D
  obtain ⟨w, hw, O, hOo, hwO⟩ := hex α hα
  obtain ⟨n, hn⟩ := hlift w hw
  obtain ⟨-, -, x, hx, -⟩ := hspec n w hn
  obtain ⟨e, -⟩ := hiso α hα w hw O hOo hwO n hn x hx
  obtain ⟨-, -, -, hinj, hrange, -⟩ := hO O hOo
  have h1 : Nat.card ↥(D.fixedRootSpan (thetaOrbit D.θ α)) = Nat.card ↥(D.fixedRootSpan O) :=
    (Nat.card_congr e.toEquiv).symm
  have h2 : Nat.card ↥(D.fixedRootSpan O) = Nat.card (D.orbitField O) := by
    have h3 : Nat.card ↥(Subtype.val '' (D.fixedRootSpan O : Set (adjointGroup τ k))) =
        Nat.card ↥(D.fixedRootSpan O) :=
      Nat.card_image_of_injective Subtype.val_injective _
    rw [← h3, ← hrange, Nat.card_range_of_injective hinj]
  have h4 : orbitCard O = (thetaOrbit D.θ α).ncard := by
    rw [← hwO]
    exact (Set.ncard_image_of_injective _ (MulAction.injective w)).symm
  rw [h1, h2, D.card_orbitField hOo, h4]

theorem gomi_fixedRootSpan_mono {Q S : Set (Fin τ.rank → ℤ)} (h : Q ⊆ S) :
    D.fixedRootSpan Q ≤ D.fixedRootSpan S := fun x hx => by
  obtain ⟨hxU, hxF⟩ := D.mem_fixedRootSpan.1 hx
  refine D.mem_fixedRootSpan.2 ⟨?_, hxF⟩
  have : rootSpan τ k Q ≤ rootSpan τ k S := iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl
  exact this hxU

theorem gomi_card_fixedRootSpan {S : Set (Fin τ.rank → ℤ)} (hSΨ : S ⊆ D.posRootsJ)
    (hθS : ∀ α ∈ S, thetaOrbit D.θ α ⊆ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S) :
    Nat.card ↥(D.fixedRootSpan S) = D.q ^ S.ncard := by
  classical
  have hSfin : S.Finite := D.finite_roots.subset fun α hα => (hSΨ hα).1
  have hSK : ∀ α ∈ S, α ∈ kernelRoots D.χ := fun α hα => (hSΨ hα).1.1
  have hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α := fun α hα =>
    ⟨isRoot_of_mem_unionRoots (hSΨ hα).1, (hSΨ hα).2⟩
  have h𝒪fin : ((thetaOrbit D.θ) '' S).Finite := hSfin.image _
  set 𝒪 : Finset (Set (Fin τ.rank → ℤ)) := h𝒪fin.toFinset with h𝒪def
  set L : List (Set (Fin τ.rank → ℤ)) := 𝒪.toList with hLdef
  have hLnd : L.Nodup := Finset.nodup_toList _
  have hL : ∀ Q, Q ∈ L ↔ ∃ γ ∈ S, Q = thetaOrbit D.θ γ := fun Q => by
    rw [hLdef, Finset.mem_toList, h𝒪def, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have hQ : ∀ Q ∈ L, ∃ γ ∈ S, Q = thetaOrbit D.θ γ := fun Q hQ' => (hL Q).1 hQ'
  have h𝒪L : ∀ Q, Q ∈ 𝒪 ↔ Q ∈ L := fun Q => (Finset.mem_toList).symm
  set enum : Set (Fin τ.rank → ℤ) → List (Fin τ.rank → ℤ) :=
    fun Q => if h : Q.Finite then h.toFinset.toList else [] with henumdef
  have henum : ∀ Q ∈ L, (enum Q).Nodup ∧ ∀ α, α ∈ enum Q ↔ α ∈ Q := fun Q hQ' => by
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    have hfin := D.finite_thetaOrbit (hSK γ hγ)
    simp only [henumdef, dite_eq_left_of_eq_true (eq_true hfin)]
    exact ⟨Finset.nodup_toList _, fun α => Finset.mem_toList.trans hfin.mem_toFinset⟩
  have horb : ∀ Q ∈ L, ∀ α ∈ Q, thetaOrbit D.θ α = Q := fun Q hQ' α hα => by
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    exact D.thetaOrbit_eq_of_mem (hSK γ hγ) hα
  set l := L.flatMap enum with hl
  have hlnd : l.Nodup := by
    refine List.nodup_flatMap.2 ⟨fun Q hQ' => (henum Q hQ').1, ?_⟩
    refine hLnd.imp_of_mem fun hQ₁ hQ₂ hne => ?_
    rw [Function.onFun, List.disjoint_left]
    intro α h₁ h₂
    exact hne ((horb _ hQ₁ α ((henum _ hQ₁).2 α |>.1 h₁)).symm.trans
      (horb _ hQ₂ α ((henum _ hQ₂).2 α |>.1 h₂)))
  have hlmem : ∀ α, α ∈ l ↔ α ∈ S := fun α => by
    rw [hl, List.mem_flatMap]
    constructor
    · rintro ⟨Q, hQ', hα⟩
      obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
      exact hθS γ hγ ((henum _ hQ').2 α |>.1 hα)
    · intro hα
      have hQ' : thetaOrbit D.θ α ∈ L := (hL _).2 ⟨α, hα, rfl⟩
      exact ⟨_, hQ', (henum _ hQ').2 α |>.2 (self_mem_thetaOrbit _ α)⟩
  have hprod : ∀ e : (Fin τ.rank → ℤ) → k, (l.map fun α => pinnedX τ k α (e α)).prod =
      (L.map fun Q => ((enum Q).map fun α => pinnedX τ k α (e α)).prod).prod := fun e => by
    rw [hl, List.map_flatMap, list_prod_flatMap]
  have hScard : S.ncard = ∑ Q ∈ 𝒪, Q.ncard := by
    have h1 : S.ncard = l.length := by
      have : S = ↑l.toFinset := by
        ext α
        simp [hlmem]
      rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hlnd]
    rw [h1, hl, List.length_flatMap]
    rw [← Finset.sum_map_toList 𝒪 (fun Q => Q.ncard)]
    refine congrArg List.sum (List.map_congr_left fun Q hQ' => ?_)
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    have hfin := D.finite_thetaOrbit (hSK γ hγ)
    simp only [henumdef, dite_eq_left_of_eq_true (eq_true hfin)]
    rw [Finset.length_toList, Set.ncard_eq_toFinset_card _ hfin]
  let G := ∀ Q : 𝒪, ↥(D.fixedRootSpan (Q : Set (Fin τ.rank → ℤ)))
  let blk : G → Set (Fin τ.rank → ℤ) → adjointGroup τ k := fun y Q =>
    if hQ' : Q ∈ 𝒪 then ((y ⟨Q, hQ'⟩ : ↥(D.fixedRootSpan Q)) : adjointGroup τ k) else 1
  have hblkmem : ∀ (y : G), ((L.map (blk y)).prod : adjointGroup τ k) ∈ D.fixedRootSpan S := by
    intro y
    refine Subgroup.list_prod_mem _ fun z hz => ?_
    obtain ⟨Q, hQ', rfl⟩ := List.mem_map.1 hz
    have hQ𝒪 : Q ∈ 𝒪 := (h𝒪L Q).2 hQ'
    obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
    simp only [blk, dif_pos hQ𝒪]
    exact gomi_fixedRootSpan_mono D (hθS γ hγ) (y ⟨_, hQ𝒪⟩).2
  let Φ : G → ↥(D.fixedRootSpan S) := fun y => ⟨(L.map (blk y)).prod, hblkmem y⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := D.exists_fixed_block_factors hSΨ hθS hclosed hLnd hL hx
    let y' : G := fun Q => ⟨y Q.1, hy Q.1 ((h𝒪L Q.1).1 Q.2)⟩
    refine ⟨y', Subtype.ext ?_⟩
    show (L.map (blk y')).prod = x
    rw [hxy]
    refine congrArg List.prod (List.map_congr_left fun Q hQ' => ?_)
    simp only [blk, y', dif_pos ((h𝒪L Q).2 hQ')]
  have hpar : ∀ y : G, ∃ c : Set (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → k, ∀ Q ∈ L,
      ((enum Q).map fun α => pinnedX τ k α (c Q α)).prod =
        (((blk y Q : adjointGroup τ k)) : ModGL τ k) := by
    intro y
    have : ∀ Q ∈ L, ∃ c' : (Fin τ.rank → ℤ) → k,
        ((enum Q).map fun α => pinnedX τ k α (c' α)).prod =
          (((blk y Q : adjointGroup τ k)) : ModGL τ k) := by
      intro Q hQ'
      have hQ𝒪 : Q ∈ 𝒪 := (h𝒪L Q).2 hQ'
      obtain ⟨hU, -⟩ := D.mem_fixedRootSpan.1 (y ⟨Q, hQ𝒪⟩).2
      obtain ⟨γ, hγ, rfl⟩ := hQ Q hQ'
      have hγK := hSK γ hγ
      have := exists_list_prod_pinnedX_eq k (fun α hα => hSpos α (hθS γ hγ hα))
        (fun α hα β hβ a b ha hb hr =>
          absurd hr (D.not_isRoot_nsmul_add_nsmul_of_mem_thetaOrbit hγK hα hβ ha hb))
        (henum _ hQ').1 (henum _ hQ').2 hU
      simp only [blk, dif_pos hQ𝒪]
      exact this
    choose! c hc using this
    exact ⟨c, hc⟩
  have hinj : Function.Injective Φ := by
    intro y₁ y₂ h12
    have h12' : (L.map (blk y₁)).prod = (L.map (blk y₂)).prod := congrArg Subtype.val h12
    obtain ⟨c₁, hc₁⟩ := hpar y₁
    obtain ⟨c₂, hc₂⟩ := hpar y₂
    set e₁ : (Fin τ.rank → ℤ) → k := fun α => c₁ (thetaOrbit D.θ α) α with he₁
    set e₂ : (Fin τ.rank → ℤ) → k := fun α => c₂ (thetaOrbit D.θ α) α with he₂
    have hblk : ∀ (c : Set (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → k) (y : G),
        (∀ Q ∈ L, ((enum Q).map fun α => pinnedX τ k α (c Q α)).prod =
          (((blk y Q : adjointGroup τ k)) : ModGL τ k)) → ∀ Q ∈ L,
        ((enum Q).map fun α => pinnedX τ k α (c (thetaOrbit D.θ α) α)).prod =
          (((blk y Q : adjointGroup τ k)) : ModGL τ k) := by
      intro c y hc Q hQ'
      rw [← hc Q hQ']
      exact congrArg List.prod (List.map_congr_left fun α hα => by
        rw [horb Q hQ' α ((henum Q hQ').2 α |>.1 hα)])
    have hlist : ∀ (c : Set (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → k) (y : G),
        (∀ Q ∈ L, ((enum Q).map fun α => pinnedX τ k α (c Q α)).prod =
          (((blk y Q : adjointGroup τ k)) : ModGL τ k)) →
        (l.map fun α => pinnedX τ k α (c (thetaOrbit D.θ α) α)).prod =
          (((L.map (blk y)).prod : adjointGroup τ k) : ModGL τ k) := by
      intro c y hc
      rw [hprod, Subgroup.val_list_prod, List.map_map]
      exact congrArg List.prod (List.map_congr_left fun Q hQ' => hblk c y hc Q hQ')
    have hE : (l.map fun α => pinnedX τ k α (e₁ α)).prod =
        (l.map fun α => pinnedX τ k α (e₂ α)).prod := by
      rw [hlist c₁ y₁ hc₁, hlist c₂ y₂ hc₂, h12']
    have hee : ∀ α ∈ l, e₁ α = e₂ α :=
      pinnedX_list_prod_injective l hlnd (fun α hα => hSpos α ((hlmem α).1 hα)) e₁ e₂ hE
    funext Q
    apply Subtype.ext
    apply Subtype.ext
    have hQL : Q.1 ∈ L := (h𝒪L Q.1).1 Q.2
    have h1 := hblk c₁ y₁ hc₁ Q.1 hQL
    have h2 := hblk c₂ y₂ hc₂ Q.1 hQL
    have hQQ : ((blk y₁ Q.1 : adjointGroup τ k) : ModGL τ k) =
        ((blk y₂ Q.1 : adjointGroup τ k) : ModGL τ k) := by
      rw [← h1, ← h2]
      exact congrArg List.prod (List.map_congr_left fun α hα => by
        have hαS : α ∈ S := by
          obtain ⟨γ, hγ, hQeq⟩ := hQ Q.1 hQL
          exact hθS γ hγ (hQeq ▸ ((henum _ hQL).2 α).1 hα)
        have hαl : α ∈ l := (hlmem α).2 hαS
        change pinnedX τ k α (e₁ α) = pinnedX τ k α (e₂ α)
        rw [hee α hαl])
    simpa [blk] using hQQ
  have hbij : Function.Bijective Φ := ⟨hinj, hsurj⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij)]
  have hfac : ∀ Q : 𝒪, Nat.card ↥(D.fixedRootSpan (Q : Set (Fin τ.rank → ℤ))) =
      D.q ^ (Q : Set (Fin τ.rank → ℤ)).ncard := by
    intro Q
    obtain ⟨γ, hγ, hQeq⟩ := hQ Q.1 ((h𝒪L Q.1).1 Q.2)
    rw [hQeq]
    exact gomi_card_fixedRootSpan_thetaOrbit D (hSΨ hγ).1
  change Nat.card (∀ Q : 𝒪, ↥(D.fixedRootSpan (Q : Set (Fin τ.rank → ℤ)))) = _
  rw [Nat.card_pi]
  simp only [hfac]
  rw [Finset.prod_coe_sort 𝒪 (fun Q => D.q ^ Q.ncard), Finset.prod_pow_eq_pow_sum, ← hScard]

theorem gomi_pow_dvd_card_orbitGroupC :
    D.q ^ D.posRootsJ.ncard ∣ Nat.card ↥D.orbitGroupC := by
  have h1 : D.fixedUnipotent = D.fixedRootSpan D.posRootsJ := by
    ext x
    rw [D.mem_fixedUnipotent, D.mem_fixedRootSpan]
    rfl
  have hcard := gomi_card_fixedRootSpan D le_rfl (fun _ hα => D.thetaOrbit_subset_posRootsJ hα)
    D.posRootsJ_closed
  rw [← h1] at hcard
  rw [← hcard]
  exact Subgroup.card_dvd_of_le D.fixedUnipotent_le_orbitGroupC

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
