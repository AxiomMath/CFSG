module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

theorem layerIn_normal_aux0 {Y : Type} [Group Y] (Chat : Subgroup Y) [Chat.Normal] (g : Y) :
    Chat.map (MulAut.conj g).toMonoidHom = Chat := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact ‹Chat.Normal›.conj_mem a ha g
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · simpa using ‹Chat.Normal›.conj_mem y hy g⁻¹
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem layerIn_normal_aux1 {Y : Type} [Group Y] (Chat : Subgroup Y) [Chat.Normal] {J : Subgroup Y}
    (hJ : CFSG.Open.IsComponentOf J Chat) (g : Y) :
    CFSG.Open.IsComponentOf (J.map (MulAut.conj g).toMonoidHom) Chat := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ‹Chat.Normal›.conj_mem a (hJ.1 ha) g
  · have h1 := hJ.2.1.map (MulAut.conj g).toMonoidHom
    rwa [layerIn_normal_aux0 Chat g] at h1
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm hJ.2.2

theorem layerIn_normal {Y : Type} [Group Y] (Chat : Subgroup Y) [Chat.Normal] :
    (layerIn Chat).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have key : layerIn Chat ≤ (layerIn Chat).comap (MulAut.conj g).toMonoidHom := by
    unfold layerIn
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (layerIn_normal_aux1 Chat hJ g)
  exact key hx

theorem exists_lift_of_cover_aux1 {X : Type} [Group X] [Finite X] (k : X) :
    ∃ a : ℕ, Odd (orderOf (k ^ (2 ^ a))) := by
  have hpos : 0 < orderOf k := orderOf_pos k
  refine ⟨(orderOf k).factorization 2, ?_⟩
  have hdvd : 2 ^ (orderOf k).factorization 2 ∣ orderOf k := Nat.ordProj_dvd _ _
  rw [orderOf_pow_of_dvd (by positivity) hdvd]
  have h2 := Nat.not_dvd_ordCompl Nat.prime_two hpos.ne'
  exact Nat.odd_iff.2 (by omega)

theorem exists_lift_of_cover_aux2 {X : Type} [Group X] (K : Subgroup X) : oddHull K ≤ K :=
  (Subgroup.closure_le K).2 fun _ hx => hx.1

theorem exists_lift_of_cover_aux3 {X : Type} [Group X] {K : Subgroup X} {x : X} (hx : x ∈ K)
    (hodd : Odd (orderOf x)) : x ∈ oddHull K :=
  Subgroup.subset_closure ⟨hx, hodd⟩

theorem exists_lift_of_cover_aux4 {X : Type} [Group X] (K : Subgroup X) :
    oddHull (oddHull K) = oddHull K := by
  apply le_antisymm (exists_lift_of_cover_aux2 _)
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem exists_lift_of_cover_aux5 {X : Type} [Group X] (K : Subgroup X) {x k : X}
    (hx : x ∈ oddHull K) (hk : k ∈ K) : k * x * k⁻¹ ∈ oddHull K := by
  have hle : oddHull K ≤ (oddHull K).comap (MulAut.conj k).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyK, hodd⟩
    show k * y * k⁻¹ ∈ oddHull K
    refine exists_lift_of_cover_aux3 (K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)) ?_
    have h1 := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
    have h2 : (MulAut.conj k).toMonoidHom y = k * y * k⁻¹ := rfl
    rw [h2] at h1
    rw [h1]
    exact hodd
  exact hle hx

theorem exists_lift_of_cover_aux6 {Z : Type} [Group Z] [Finite Z] (E N : Subgroup Z) (hN : N ≤ E)
    [(N.subgroupOf E).Normal] (hE : ⁅E, E⁆ = E) (h2 : ∀ e ∈ E, ∃ a : ℕ, e ^ (2 ^ a) ∈ N) :
    E ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.2 hE
  have hQ2 : IsPGroup 2 (↥E ⧸ N.subgroupOf E) := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := h2 e.1 e.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  haveI : Group.IsNilpotent (↥E ⧸ N.subgroupOf E) := hQ2.isNilpotent
  have hsub : Subsingleton (↥E ⧸ N.subgroupOf E) := by
    by_contra hns
    haveI : Nontrivial (↥E ⧸ N.subgroupOf E) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable (↥E ⧸ N.subgroupOf E) inferInstance
  intro e he
  have h1 : (QuotientGroup.mk ⟨e, he⟩ : ↥E ⧸ N.subgroupOf E) = 1 := Subsingleton.elim _ _
  have h3 : (⟨e, he⟩ : ↥E) ∈ N.subgroupOf E :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf E) ⟨e, he⟩).1 h1
  exact h3

theorem exists_lift_of_cover {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hle : CFSG.pCore 2 X ≤ gnC T) {Ls : Subgroup (X ⧸ gnC T)}
    (Ebar : Subgroup (X ⧸ CFSG.pCore 2 X)) (hE : CFSG.Open.IsComponentOf Ebar ⊤)
    (hEs : Ebar.map (barToStar T hle) = Ls) : ∃ L : Subgroup X, LiftOf T L Ls := by
  classical
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    QuotientGroup.mk'_surjective _
  have hKsub : CFSG.Open.IsSubnormal (Ebar.comap (QuotientGroup.mk' (CFSG.pCore 2 X))) ⊤ :=
    isSubnormal_comap _ hE.2.1
  set K : Subgroup X := Ebar.comap (QuotientGroup.mk' (CFSG.pCore 2 X)) with hK
  have hLK : oddHull K ≤ K := exists_lift_of_cover_aux2 K
  have hLnorm : ((oddHull K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLK]
    intro x k hx hk
    exact exists_lift_of_cover_aux5 K hx hk
  have hsubn : CFSG.Open.IsSubnormal (oddHull K) ⊤ :=
    CFSG.Open.IsSubnormal.step hLK hLnorm hKsub
  have hNE : (oddHull K).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ Ebar :=
    calc (oddHull K).map (QuotientGroup.mk' (CFSG.pCore 2 X))
        ≤ K.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := Subgroup.map_mono hLK
      _ = Ebar := Subgroup.map_comap_eq_self_of_surjective hsurj Ebar
  have hEK : ∀ e ∈ Ebar, ∃ k ∈ K, QuotientGroup.mk' (CFSG.pCore 2 X) k = e := by
    intro e he
    obtain ⟨x, rfl⟩ := hsurj e
    exact ⟨x, he, rfl⟩
  haveI : (((oddHull K).map (QuotientGroup.mk' (CFSG.pCore 2 X))).subgroupOf Ebar).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNE]
    rintro _ e ⟨l, hl, rfl⟩ he
    obtain ⟨k, hk, rfl⟩ := hEK e he
    exact ⟨k * l * k⁻¹, exists_lift_of_cover_aux5 K hl hk, by simp [map_mul, map_inv]⟩
  have hmapL : (oddHull K).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = Ebar := by
    refine le_antisymm hNE ?_
    refine exists_lift_of_cover_aux6 Ebar _ hNE (commutator_eq_self_of_isQuasisimple hE.2.2) ?_
    intro e he
    obtain ⟨k, hk, rfl⟩ := hEK e he
    obtain ⟨a, ha⟩ := exists_lift_of_cover_aux1 k
    refine ⟨a, ?_⟩
    rw [← map_pow]
    exact ⟨k ^ 2 ^ a, exists_lift_of_cover_aux3 (K.pow_mem hk _) ha, rfl⟩
  refine ⟨oddHull K, ⟨hsubn, exists_lift_of_cover_aux4 K, ?_⟩, ?_⟩
  · rw [hmapL]
    exact hE
  · have hcomp : toStar T = (barToStar T hle).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) := rfl
    rw [hcomp, ← Subgroup.map_map, hmapL, hEs]

theorem card_le_pRank_of_components_aux1_gen {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr : r.Prime)
    (A : Subgroup Y) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {k : ℕ} {Q : Type} [Group Q] (hQcard : Nat.card Q = r ^ k) (hQexp : ∀ q : Q, q ^ r = 1)
    (ψ : ↥A →* Q) (hψ : Function.Surjective ψ) {H : Subgroup Y} (hAH : A ≤ H) :
    k ≤ CFSG.Open.pRank r H := by
  haveI : Fact r.Prime := ⟨hr⟩
  let pw : ↥A →* ↥A :=
    { toFun := fun a => a ^ r
      map_one' := one_pow r
      map_mul' := fun a b =>
        (show Commute a b from Subtype.ext (hcomm a.1 a.2 b.1 b.2)).mul_pow r }
  have h1 : Nat.card ↥pw.ker * Nat.card ↥pw.range = Nat.card ↥A :=
    Subgroup.card_ker_mul_card_range pw
  have hRle : pw.range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    show ψ (a ^ r) = 1
    rw [map_pow, hQexp]
  have hidx : ψ.ker.index = r ^ k := by
    rw [Subgroup.index_ker, ← hQcard, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top]
  have h2 : ψ.ker.index ∣ pw.range.index := Subgroup.index_dvd_of_le hRle
  have h3 : pw.range.index = Nat.card ↥pw.ker := by
    have h4 := Subgroup.index_mul_card pw.range
    have hpos : 0 < Nat.card ↥pw.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h4.trans h1.symm)
  rw [hidx, h3] at h2
  have hWexp : ∀ w : ↥pw.ker, w ^ r = 1 := by
    intro w
    apply Subtype.ext
    have hw : pw w.1 = 1 := w.2
    exact hw
  have hWp : IsPGroup r ↥pw.ker := fun w => ⟨1, by simpa using hWexp w⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hWp
  rw [hm] at h2
  have hkm : k ≤ m := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 h2
  refine hkm.trans ?_
  refine CFSG.SectionRank.le_pRank_of_injective (G := Y) hr.one_lt
    (fun a b => Subtype.ext (Subtype.ext (hcomm a.1.1 a.1.2 b.1.1 b.1.2))) hWexp hm
    (A.subtype.comp pw.ker.subtype) ?_ ?_
  · exact Subtype.val_injective.comp Subtype.val_injective
  · rintro _ ⟨w, rfl⟩
    exact hAH w.1.2

theorem card_le_pRank_of_components_aux2 {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (G ⧸ Subgroup.center G)) :
    ∃ x : G, x ∉ Subgroup.center G ∧ ∃ n : ℕ, x ^ (r ^ n) = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r G))
  by_contra hcon
  push Not at hcon
  have hPle : (P : Subgroup G) ≤ Subgroup.center G := by
    intro x hx
    by_contra hxZ
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
    exact hcon x hxZ n (by simpa using congrArg Subtype.val hn)
  have h1 : Nat.card (P : Subgroup G) ∣ Nat.card (Subgroup.center G) :=
    Subgroup.card_dvd_of_le hPle
  rw [Sylow.card_eq_multiplicity] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
  apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := G)).ne' hr
  rw [pow_succ]
  calc r ^ (Nat.card G).factorization r * r
      ∣ Nat.card (Subgroup.center G) * Nat.card (G ⧸ Subgroup.center G) := Nat.mul_dvd_mul h1 hdvd
    _ = Nat.card G := by rw [mul_comm]; exact h2.symm

theorem card_le_pRank_of_components_aux3 {G : Type} [Group G] {r : ℕ} (hr : r.Prime) {x : G} {a : ℕ}
    (hx : x ^ (r ^ a) = 1) (Z : Subgroup G) (hxZ : x ∉ Z) {n : ℤ} (hnZ : x ^ n ∈ Z) :
    (r : ℤ) ∣ n := by
  by_contra hrn
  have hcop : IsCoprime ((r : ℤ) ^ a) n :=
    ((Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hr).irreducible).2 hrn).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  apply hxZ
  have hxr : x ^ ((r : ℤ) ^ a) = 1 := by
    have h1 : ((r : ℤ) ^ a) = ((r ^ a : ℕ) : ℤ) := by push_cast; rfl
    rw [h1, zpow_natCast, hx]
  have h1 : x = (x ^ n) ^ v := by
    calc x = x ^ (u * (r : ℤ) ^ a + v * n) := by rw [huv, zpow_one]
      _ = (x ^ ((r : ℤ) ^ a)) ^ u * (x ^ n) ^ v := by
        rw [zpow_add, mul_comm u, zpow_mul, mul_comm v, zpow_mul]
      _ = (x ^ n) ^ v := by rw [hxr, one_zpow, one_mul]
  rw [h1]
  exact Z.zpow_mem hnZ v

theorem card_le_pRank_of_components_gen {Y : Type} [Group Y] [Finite Y] (S : Finset (Subgroup Y))
    (hS : ∀ J ∈ S, CFSG.Open.IsComponentOf J ⊤) (H : Subgroup Y)
    (hSH : ∀ J ∈ S, J ≤ H) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hdvd : ∀ J ∈ S, r ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    S.card ≤ CFSG.Open.pRank r H := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hex : ∀ J : ↥S, ∃ x : Y, x ∈ J.1 ∧ x ∉ Subgroup.centralizer (J.1 : Set Y) ∧
      ∃ a : ℕ, x ^ (r ^ a) = 1 := by
    intro J
    obtain ⟨x, hxZ, a, hxa⟩ := card_le_pRank_of_components_aux2 hr (hdvd J.1 J.2)
    refine ⟨x.1, x.2, fun hc => hxZ ?_, a, by simpa using congrArg Subtype.val hxa⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) g.1 g.2)
  choose x hxJ hxZ hxa using hex
  have hcommJ : ∀ J J' : ↥S, J ≠ J' → ∀ a ∈ J.1, ∀ b ∈ J'.1, a * b = b * a := by
    intro J J' hne a ha b hb
    have h1 := kComp_holds.1 Y J.1 J'.1 (hS J.1 J.2) (hS J'.1 J'.2) (fun h => hne (Subtype.ext h))
    have h2 : ⁅a, b⁆ ∈ ⁅J.1, J'.1⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h1, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  let φ : ∀ J : ↥S, Multiplicative ℤ →* Y := fun J => zpowersHom Y (x J)
  have hφJ : ∀ (J : ↥S) (n : Multiplicative ℤ), φ J n ∈ J.1 := fun J n =>
    Subgroup.zpow_mem _ (hxJ J) _
  have hφ : Pairwise fun J J' : ↥S => ∀ (m : Multiplicative ℤ) (m' : Multiplicative ℤ),
      Commute (φ J m) (φ J' m') :=
    fun J J' hne m m' => hcommJ J J' hne _ (hφJ J m) _ (hφJ J' m')
  let Ψ : (↥S → Multiplicative ℤ) →* Y := MonoidHom.noncommPiCoprod φ hφ
  have hext : ∀ (g : ↥S → Multiplicative ℤ) (J₀ : ↥S), ∃ P : Y,
      Ψ g = φ J₀ (g J₀) * P ∧ ∀ y ∈ J₀.1, Commute y P := by
    intro g J₀
    have hcomm : (↑(Finset.univ : Finset ↥S) : Set ↥S).Pairwise
        (Function.onFun Commute fun i => φ i (g i)) :=
      Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ hφ a (g i) (g j)) _
    refine ⟨(Finset.univ.erase J₀).noncommProd (fun i => φ i (g i))
      (hcomm.mono (Finset.coe_subset.2 (Finset.erase_subset _ _))), ?_, ?_⟩
    · rw [MonoidHom.noncommPiCoprod_apply]
      exact (Finset.mul_noncommProd_erase _ (Finset.mem_univ J₀) _ hcomm).symm
    · intro y hy
      refine Finset.noncommProd_commute _ _ _ y (fun i hi => ?_)
      have hne : J₀ ≠ i := fun h => (Finset.mem_erase.1 hi).1 h.symm
      exact hcommJ J₀ i hne y hy _ (hφJ i _)
  have hker : ∀ g : ↥S → Multiplicative ℤ, Ψ g = 1 → ∀ J : ↥S,
      (r : ℤ) ∣ Multiplicative.toAdd (g J) := by
    intro g hg J₀
    obtain ⟨P, hP, hPc⟩ := hext g J₀
    rw [hg] at hP
    have h1 : φ J₀ (g J₀) = P⁻¹ := eq_inv_of_mul_eq_one_left hP.symm
    have h2 : x J₀ ^ (g J₀).toAdd ∈ Subgroup.centralizer (J₀.1 : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h3 : Commute y P⁻¹ := (hPc y hy).inv_right
      have h4 : φ J₀ (g J₀) = x J₀ ^ (g J₀).toAdd := zpowersHom_apply Y (x J₀) (g J₀)
      rw [← h4, h1]
      exact h3
    obtain ⟨a, ha⟩ := hxa J₀
    exact card_le_pRank_of_components_aux3 hr ha _ (hxZ J₀) h2
  let q : Multiplicative ℤ →* Multiplicative (ZMod r) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod r))
  let Q : (↥S → Multiplicative ℤ) →* (↥S → Multiplicative (ZMod r)) := MonoidHom.compLeft q ↥S
  have hkerQ : Ψ.rangeRestrict.ker ≤ Q.ker := by
    intro g hg
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    funext J
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (g J).toAdd r).2 (hker g hg J)
    show Multiplicative.ofAdd (((g J).toAdd : ℤ) : ZMod r) = 1
    rw [h1]
    rfl
  have hQsurj : Function.Surjective Q := by
    intro y
    choose c hc using fun J => ZMod.intCast_surjective (n := r) (y J).toAdd
    refine ⟨fun J => Multiplicative.ofAdd (c J), ?_⟩
    funext J
    show Multiplicative.ofAdd (((c J : ℤ) : ZMod r)) = y J
    rw [hc J]
    rfl
  have hQexp : ∀ y : ↥S → Multiplicative (ZMod r), y ^ r = 1 := by
    intro y
    funext J
    show (y J) ^ r = 1
    rw [← ofAdd_toAdd (y J), ← ofAdd_nsmul]
    simp
  have hQcard : Nat.card (↥S → Multiplicative (ZMod r)) = r ^ S.card := by
    rw [Nat.card_pi]
    simp [Nat.card_zmod]
  have hAcomm : ∀ a ∈ Ψ.range, ∀ b ∈ Ψ.range, a * b = b * a := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm g g']
  let ψ := Ψ.rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective Ψ) ⟨Q, hkerQ⟩
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := hQsurj y
    refine ⟨Ψ.rangeRestrict g, ?_⟩
    have h1 := MonoidHom.liftOfRightInverse_comp_apply Ψ.rangeRestrict _
      (Function.rightInverse_surjInv (MonoidHom.rangeRestrict_surjective Ψ)) ⟨Q, hkerQ⟩ g
    rw [← hg]
    exact h1
  have hΨH : Ψ.range ≤ H := by
    rintro _ ⟨g, rfl⟩
    rw [MonoidHom.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _ fun J _ => hSH J.1 J.2 (hφJ J (g J))
  exact card_le_pRank_of_components_aux1_gen hr Ψ.range hAcomm hQcard hQexp ψ hψ hΨH

theorem perfect_le_normalizer_component_aux1 {W : Type} [Group W] [Finite W]
    (h : CFSG.Open.IsQuasisimple W) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card (W ⧸ Subgroup.center W) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup (W ⧸ Subgroup.center W) := h.2
  by_contra hcon
  push Not at hcon
  have hpos : Nat.card (W ⧸ Subgroup.center W) ≠ 0 := Nat.card_pos.ne'
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := 2) (fun {d} hd hdn => by
    by_contra hd2
    exact hcon d hd hd2 hdn)
  have hp2 : IsPGroup 2 (W ⧸ Subgroup.center W) := IsPGroup.of_card hpow
  haveI : Group.IsNilpotent (W ⧸ Subgroup.center W) := hp2.isNilpotent
  haveI : IsMulCommutative (W ⧸ Subgroup.center W) :=
    ⟨⟨fun a b => IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b⟩⟩
  exact quotient_center_nonabelian_of_isQuasisimple h inferInstance

theorem perfect_le_normalizer_component_aux2 {Y : Type} [Group Y] (J : Subgroup Y) (g : Y) :
    Nat.card (↥(J.map (MulAut.conj g).toMonoidHom) ⧸
        Subgroup.center ↥(J.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  let e := J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥J)
    (Subgroup.center ↥(J.map (MulAut.conj g).toMonoidHom)) e (Subgroup.map_center_eq e)).toEquiv).symm

open scoped Pointwise in
theorem perfect_le_normalizer_component_aux3 {Y : Type} [Group Y] (K : Subgroup Y) (g : Y) :
    ConjAct.toConjAct g • K = K.map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [ConjAct.toConjAct_smul, MulAut.conj_apply]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [ConjAct.toConjAct_smul, MulAut.conj_apply]⟩

theorem perfect_le_normalizer_component_aux4 {Y : Type} [Group Y] (Chat : Subgroup Y) [Chat.Normal]
    {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K Chat) : CFSG.Open.IsComponentOf K ⊤ :=
  ⟨le_top, hK.2.1.trans (CFSG.Open.IsSubnormal.step le_top inferInstance
    (CFSG.Open.IsSubnormal.refl ⊤)), hK.2.2⟩

open scoped Pointwise in
theorem perfect_le_normalizer_component_gen {Y : Type} [Group Y] [Finite Y]
    (Chat : Subgroup Y) [Chat.Normal]
    (hrkC : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r Chat ≤ 3)
    (E : Subgroup Y) (hE : ⁅E, E⁆ = E)
    (J : Subgroup Y) (hJ : CFSG.Open.IsComponentOf J Chat) :
    E ≤ Subgroup.normalizer (J : Set Y) := by
  classical
  obtain ⟨r, hr, hr2, hrJ⟩ := perfect_le_normalizer_component_aux1 (W := ↥J) hJ.2.2
  letI : MulAction ↥E (Subgroup Y) :=
    MulAction.compHom (Subgroup Y)
      ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp E.subtype)
  have hsmul : ∀ (e : ↥E) (K : Subgroup Y), e • K = K.map (MulAut.conj (e : Y)).toMonoidHom :=
    fun e K => perfect_le_normalizer_component_aux3 K e.1
  have hOfin : (MulAction.orbit ↥E J).Finite := Set.toFinite _
  have hOcomp : ∀ K ∈ MulAction.orbit ↥E J, CFSG.Open.IsComponentOf K Chat := by
    rintro K ⟨e, rfl⟩
    show CFSG.Open.IsComponentOf (e • J) Chat
    rw [hsmul]
    exact layerIn_normal_aux1 Chat hJ e.1
  have hOdvd : ∀ K ∈ MulAction.orbit ↥E J, r ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rintro K ⟨e, rfl⟩
    show r ∣ Nat.card (↥(e • J) ⧸ Subgroup.center ↥(e • J))
    rw [hsmul, perfect_le_normalizer_component_aux2]
    exact hrJ
  have hScard : hOfin.toFinset.card ≤ 3 :=
    (card_le_pRank_of_components_gen hOfin.toFinset
      (fun K hK => perfect_le_normalizer_component_aux4 Chat (hOcomp K (hOfin.mem_toFinset.1 hK)))
      Chat (fun K hK => (hOcomp K (hOfin.mem_toFinset.1 hK)).1)
      hr hr2 (fun K hK => hOdvd K (hOfin.mem_toFinset.1 hK))).trans (hrkC r hr hr2)
  have hcardO : Nat.card ↥(MulAction.orbit ↥E J) ≤ 4 := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hOfin]
    omega
  haveI : Group.IsSolvable (Equiv.Perm ↥(MulAction.orbit ↥E J)) := Equiv.Perm.isSolvable hcardO
  let ρ : ↥E →* Equiv.Perm ↥(MulAction.orbit ↥E J) :=
    MulAction.toPermHom ↥E ↥(MulAction.orbit ↥E J)
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.2 hE
  haveI : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  have hsub : Subsingleton ↥ρ.range := by
    by_contra hns
    haveI : Nontrivial ↥ρ.range := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable ↥ρ.range inferInstance
  intro e he
  have h1 : ρ ⟨e, he⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨ρ ⟨e, he⟩, ⟨_, rfl⟩⟩ : ↥ρ.range) 1)
  have h2 : (⟨e, he⟩ : ↥E) • J = J := by
    have h3 : (ρ ⟨e, he⟩) ⟨J, MulAction.mem_orbit_self J⟩ = ⟨J, MulAction.mem_orbit_self J⟩ := by
      rw [h1]
      rfl
    exact congrArg Subtype.val h3
  exact Subgroup.conjAct_pointwise_smul_iff.1 h2

end CFSG.LocalAnalysis.RankThreeUC.S15
