module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic
import CFSG.Quasithin.Background.G8Dihedral
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open Subgroup

open scoped commutatorElement

section CaseA

variable {X : Type} [Group X] [Finite X] {K : Type} [Group K]

theorem i1020_pi_elemAbelian {V : Subgroup K} (hV : IsElemAbelian 2 V) {k : ℕ}
    (hVc : Nat.card V = 2 ^ k) (r : ℕ) :
    IsElemAbelian 2 (Subgroup.pi Set.univ fun _ : Fin r => V) ∧
      Nat.card (Subgroup.pi Set.univ fun _ : Fin r => V) = 2 ^ (k * r) := by
  have := hV.1
  refine ⟨⟨?_, fun f hf => ?_⟩, ?_⟩
  · rw [← le_centralizer_iff_isMulCommutative]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    funext j
    exact setLike_mul_comm ((mem_pi _).1 hb j (Set.mem_univ _)) ((mem_pi _).1 ha j (Set.mem_univ _))
  · funext j
    exact hV.2 _ ((mem_pi _).1 hf j (Set.mem_univ _))
  · have e : (Subgroup.pi Set.univ fun _ : Fin r => V) ≃ (Fin r → V) :=
      { toFun := fun f j => ⟨(f : Fin r → K) j, (mem_pi _).1 f.2 j (Set.mem_univ _)⟩
        invFun := fun g => ⟨fun j => g j, (mem_pi _).2 fun j _ => (g j).2⟩
        left_inv := fun f => rfl
        right_inv := fun g => rfl }
    rw [Nat.card_congr e, Nat.card_pi, hVc, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]

theorem i1020_caseA {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {k : ℕ} (hk : 2 ≤ k) {V : Subgroup K}
    (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ k) {r : ℕ} (hr : 1 ≤ r)
    (φ : X →* (Fin r → K)) (hφ : Function.Surjective φ) (hY : IsPGroup q φ.ker)
    (hYne : φ.ker ≠ ⊥) (hC : centralizer (φ.ker : Set X) ≤ φ.ker) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ S ≠ ⊥ ∧ ∃ E : Subgroup X, E ≤ normalizer (S : Set X) ∧
      IsElemAbelian q E ∧ Nat.card E = q ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hTbar, hTbarc⟩ := i1020_pi_elemAbelian hV hVc r
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hY
  have hYodd : Odd (Nat.card φ.ker) := by rw [ha]; exact (hq.odd_of_ne_two hq2).pow
  obtain ⟨T, -, hT, hTc⟩ := i1020_coprime_lift (p := 2) φ ⊤
    (by rw [top_inf_eq]; exact hYodd.not_two_dvd_nat)
    (by rw [map_top_of_surjective φ hφ]; exact le_top) hTbar hTbarc
  have hTY : T ⊓ φ.ker = ⊥ := by
    rw [← disjoint_iff]
    refine disjoint_of_coprime_natCard ?_
    rw [hTc, ha]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hfaith : T ⊓ centralizer (φ.ker : Set X) = ⊥ :=
    le_bot_iff.1 (hTY ▸ inf_le_inf_left T hC)
  have h81 : CFSG.Quasithin.G81 φ.ker T T :=
    ⟨hT, le_rfl, IsPGroup.of_card hTc, le_normalizer_of_normal, hY.isNilpotent, hYodd, hYne⟩
  have hkr : 2 * r ≤ k * r := Nat.mul_le_mul_right r hk
  have hn : 0 < k * r := by omega
  obtain ⟨Hs, p, hDF, -, -, hx⟩ := CFSG.Quasithin.g8_6 h81 hn hTc hfaith
  choose x hxY hxH hxo using hx
  have hp : ∀ i, p i = q := by
    intro i
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hY ⟨x i, hxY i⟩
    rw [orderOf_mk, hxo i] at hm
    have h1 : p i ∣ q ^ m := hm ▸ dvd_rfl
    exact (Nat.prime_dvd_prime_iff_eq (hDF.prime i) hq).1 ((hDF.prime i).dvd_of_dvd_pow h1)
  set i0 : Fin (k * r) := ⟨0, hn⟩
  obtain ⟨e⟩ := hDF.iso i0
  set t : X := (e.symm (DihedralGroup.sr 0) : X) with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have htH : t ∈ Hs i0 := (e.symm (DihedralGroup.sr 0)).2
  let emb : Fin r → Fin (k * r) := fun j => ⟨j + 1, by omega⟩
  have hemb_inj : Function.Injective emb := by
    intro j j' h
    have := congrArg Fin.val h
    simp only [emb] at this
    exact Fin.ext (by omega)
  have hemb0 : ∀ j, emb j ≠ i0 := by
    intro j h
    have := congrArg Fin.val h
    simp [emb, i0] at this
  obtain ⟨hE, hEc⟩ := i1020_family (fun j => x (emb j)) (fun j => (hxo _).trans (hp _))
    (fun j j' hjj' => hDF.commute _ _ (hemb_inj.ne hjj') _ (hxH _) _ (hxH _))
    ((hDF.independent.comp hemb_inj).mono fun j => zpowers_le.2 (hxH (emb j)))
  refine ⟨zpowers t, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), ?_,
    ⨆ j, zpowers (x (emb j)), ?_, hE, by rw [hEc, Fintype.card_fin]⟩
  · intro hbot
    have : t ∈ (⊥ : Subgroup X) := hbot ▸ mem_zpowers t
    rw [mem_bot] at this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · refine iSup_le fun j => zpowers_le.2 (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (hDF.commute _ _ (hemb0 j).symm t htH _ (hxH _)) m).eq

end CaseA

section CaseB

variable {X : Type} [Group X] [Finite X] {K : Type} [Group K]

theorem i1020_commutator_top [IsSimpleGroup K] (hnc : ∃ a b : K, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  rw [← commutator_def]
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K)).resolve_left fun h => ?_
  obtain ⟨a, b, hab⟩ := hnc
  have hc := (commutator_eq_bot_iff_center_eq_top K).1 h
  have : b ∈ center K := hc ▸ mem_top b
  exact hab (mem_center_iff.1 this a)

theorem i1020_exists_orderOf_not_mem {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L Y : Subgroup X}
    (hLperf : ⁅L, L⁆ = L) (hLY : L ≤ centralizer (Y : Set X)) (hqL : q ∣ Nat.card L) :
    ∃ x ∈ L, orderOf x = q ∧ x ∉ Y := by
  have : Fact q.Prime := ⟨hq⟩
  by_contra hno
  push Not at hno
  have hcen : ∀ x : L, orderOf x = q → x ∈ center L := by
    intro x hx
    have hxY : (x : X) ∈ Y := hno x x.2 (by rw [orderOf_coe, hx])
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 (hLY g.2) x hxY).symm
  obtain ⟨N, hN, hcop, hquot⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.hasNormalPComplement_of_central_order_p
      hq2 hcen
  have hLp : Group.IsPerfect L := Subgroup.isPerfect_iff.2 hLperf
  have hsub : Subsingleton (L ⧸ N) := by
    by_contra hns
    have hnt : Nontrivial (L ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (G := L ⧸ N) hquot.isNilpotent
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  rw [hNtop, card_top] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd hq |>.1 hcop) hqL

theorem i1020_caseB [IsSimpleGroup K] (hnc : ∃ a b : K, a * b ≠ b * a) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqK : q ∣ Nat.card K) {r : ℕ} (φ : X →* (Fin r → K))
    (hφ : Function.Surjective φ) (hC : ¬ centralizer (φ.ker : Set X) ≤ φ.ker) :
    ∃ i : Fin r, ∃ x : X, orderOf x = q ∧ φ x i ≠ 1 ∧ ∀ h : X, φ h i = 1 → x * h = h * x := by
  classical
  set Y : Subgroup X := φ.ker with hYdef
  set C : Subgroup X := centralizer (Y : Set X)
  have hCn : (C.map φ).Normal := Subgroup.normal_centralizer.map φ hφ
  have hCne : C.map φ ≠ ⊥ := fun h => hC ((Subgroup.map_eq_bot_iff _).1 h)
  obtain ⟨i, hi⟩ := i1020_exists_mulSingle_mem hnc hCn hCne
  set ψ : X →* K := (Pi.evalMonoidHom (fun _ : Fin r => K) i).comp φ with hψdef
  let good : Subgroup X → Prop := fun M =>
    M ≤ C ∧ (∀ m ∈ M, ∀ j, j ≠ i → φ m j = 1) ∧ M.map ψ = ⊤
  have hgood0 : good (C ⊓ (Subgroup.pi {j | j ≠ i} fun _ => (⊥ : Subgroup K)).comap φ) := by
    refine ⟨inf_le_left, fun m hm j hj => ?_, ?_⟩
    · have := (mem_pi _).1 (mem_comap.1 (mem_inf.1 hm).2) j hj
      rwa [mem_bot] at this
    · rw [eq_top_iff]
      intro a _
      obtain ⟨c, hc, hca⟩ := mem_map.1 (hi a)
      refine ⟨c, mem_inf.2 ⟨hc, mem_comap.2 ((mem_pi _).2 fun j hj => ?_)⟩, ?_⟩
      · rw [hca, Pi.mulSingle_eq_of_ne hj, mem_bot]
      · simp [hψdef, hca]
  have hex : ∃ n, ∃ M, good M ∧ Nat.card M = n := ⟨_, _, hgood0, rfl⟩
  obtain ⟨L, hL, hLc⟩ := Nat.find_spec hex
  have hLmin : ∀ M, good M → Nat.card L ≤ Nat.card M := fun M hM =>
    hLc ▸ Nat.find_min' hex ⟨M, hM, rfl⟩
  obtain ⟨hLC, hLi, hLψ⟩ := hL
  have hLperf : ⁅L, L⁆ = L := by
    have hle : ⁅L, L⁆ ≤ L := commutator_le_self L
    refine eq_of_le_of_card_ge hle (hLmin _ ⟨hle.trans hLC, fun m hm => hLi m (hle hm), ?_⟩)
    rw [map_commutator, hLψ, i1020_commutator_top hnc]
  have hqL : q ∣ Nat.card L := by
    refine hqK.trans ?_
    have h1 := card_map_dvd L ψ
    rwa [hLψ, card_top] at h1
  obtain ⟨x, hxL, hxo, hxY⟩ := i1020_exists_orderOf_not_mem hq hq2 hLperf hLC hqL
  refine ⟨i, x, hxo, fun hxi => hxY ?_, fun h hh => ?_⟩
  · rw [hYdef, MonoidHom.mem_ker]
    funext j
    by_cases hj : j = i
    · subst hj; exact hxi
    · exact hLi x hxL j hj
  ·
    have hLH : ⁅L, ψ.ker⁆ ≤ Y := by
      rw [commutator_le]
      intro l hl g hg
      rw [hYdef, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      funext j
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      by_cases hj : j = i
      · subst hj
        have : φ g j = 1 := hg
        simp [this]
      · simp [hLi l hl j hj]
    have hYL : ⁅Y, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hLC)
    have h1 : ⁅⁅L, ψ.ker⁆, L⁆ = ⊥ := le_bot_iff.1 (hYL ▸ commutator_mono hLH le_rfl)
    have h2 : ⁅⁅ψ.ker, L⁆, L⁆ = ⊥ := by rw [commutator_comm ψ.ker L]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hLperf] at h3
    have h4 : ⁅x, h⁆ ∈ ⁅L, ψ.ker⁆ := commutator_mem_commutator hxL (by simpa [hψdef] using hh)
    rw [h3, mem_bot] at h4
    exact commutatorElement_eq_one_iff_mul_comm.1 h4

end CaseB

end CFSG.HardMathSupport.Solomon.Coordinator
