module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.ChevThree
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParLift
public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.Quasithin.Background.E1Amb
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusion

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

section Subnormal

variable {G : Type*} [Group G]

private theorem le_normalizer_of_conj_mem {S M : Subgroup G}
    (h : ∀ g ∈ S, ∀ x ∈ M, g * x * g⁻¹ ∈ M) : S ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h g hg y, fun hy => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hy
  simpa [mul_assoc] using this

private theorem isSubnormal_of_le_centralizer {A U L : Subgroup G} (hAU : A ≤ U) (hUL : U ≤ L)
    (hUc : U ≤ Subgroup.centralizer (L : Set G)) (hL : IsSubnormal L ⊤) : IsSubnormal A ⊤ := by
  have hUA : U ≤ Subgroup.normalizer (A : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (hUc (hAU ha)) u (hUL hu)).symm)
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hUc hu) l hl).symm)
  exact IsSubnormal.step hAU ((Subgroup.normal_subgroupOf_iff_le_normalizer hAU).2 hUA)
    (IsSubnormal.step hUL ((Subgroup.normal_subgroupOf_iff_le_normalizer hUL).2 hLU) hL)

end Subnormal

section Centre

private theorem exists_minimal_invariant {G : Type*} [Group G] [Finite G] {S A : Subgroup G}
    (hA0 : A ≠ ⊥) (hSA : S ≤ Subgroup.normalizer (A : Set G)) :
    ∃ U : Subgroup G, U ≤ A ∧ U ≠ ⊥ ∧ S ≤ Subgroup.normalizer (U : Set G) ∧
      ∀ V : Subgroup G, V ≤ U → S ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = U := by
  obtain ⟨U, hUA, ⟨hU0, hSU⟩, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun V : Subgroup G => V ≠ ⊥ ∧ S ≤ Subgroup.normalizer (V : Set G)) A ⟨hA0, hSA⟩
  refine ⟨U, hUA, hU0, hSU, fun V hVU hSV => ?_⟩
  by_cases hV : V = ⊥
  · exact Or.inl hV
  · exact Or.inr (le_antisymm hVU (hmin ⟨hV, hSV⟩ hVU))

private theorem minParabolic_sup_of_minimal {G : Type*} [Group G] [Finite G] {S U : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsPGroup 2 S)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hUp : ∀ x ∈ U, x ^ p = 1) (hU0 : U ≠ ⊥)
    (hUc : ¬ U ≤ Subgroup.centralizer (S : Set G))
    (hmin : ∀ V : Subgroup G, V ≤ U → S ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = U) :
    MinParabolic (U ⊔ S) S S := by
  have : Fact p.Prime := ⟨hp⟩
  have hUS : ∀ x ∈ U, x ∈ S → x = 1 := by
    intro x hxU hxS
    obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.1 (E1.mem_of_pow_mem_two_p (N := ⊥) hp hp2 (k := 1) (j := k)
      (by simpa using hUp x hxU) (by simpa using hk'))
  have hUS' : U ⊓ S = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x hx => hUS x hx.1 hx.2
  have hUpg : IsPGroup p ↥U := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : g ^ p = 1 := Subtype.ext (by simpa using hUp g g.2)
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hg) with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hodd : ¬ 2 ∣ S.relIndex (U ⊔ S) := by
    have h := B6.relIndex_inf_eq_relIndex_sup hSU
    rw [sup_comm U S, ← h, inf_comm, hUS', Subgroup.relIndex_bot_left]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hUpg
    rw [hn]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hclaim : ∀ K : Subgroup G, S ≤ K → K ≤ U ⊔ S → K = S ∨ K = U ⊔ S := by
    intro K hSK hKUS
    have hSV : S ≤ Subgroup.normalizer ((K ⊓ U : Subgroup G) : Set G) := fun s hs =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hSK hs), hSU hs⟩
    rcases hmin (K ⊓ U) inf_le_right hSV with h | h
    · left
      refine le_antisymm (fun k hk => ?_) hSK
      have hk' : k ∈ (U : Set G) * (S : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left U S hSU]
        exact hKUS hk
      obtain ⟨u, hu, s, hs, rfl⟩ := hk'
      have huK : u ∈ K := by simpa using K.mul_mem hk (K.inv_mem (hSK hs))
      have huB : u ∈ K ⊓ U := ⟨huK, hu⟩
      rw [h, Subgroup.mem_bot] at huB
      show u * s ∈ S
      rw [huB, one_mul]
      exact hs
    · right
      have hUK : U ≤ K := fun u hu => by
        have : u ∈ K ⊓ U := by rw [h]; exact hu
        exact this.1
      exact le_antisymm hKUS (sup_le hUK hSK)
  have hlt : S < U ⊔ S := lt_of_le_of_ne le_sup_right fun h => by
    apply hU0
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => hUS u hu ?_
    rw [h]
    exact Subgroup.mem_sup_left hu
  refine ⟨⟨le_sup_right, hS, hodd⟩, fun hnorm => ?_, ?_⟩
  ·
    apply hUc
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hu' : u ∈ Subgroup.normalizer (S : Set G) := hnorm (Subgroup.mem_sup_left hu)
    have h1 : u * s * u⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hu' s).mp hs
    have h2 : s * u⁻¹ * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hSU hs) u⁻¹).mp (U.inv_mem hu)
    have hcU : u * s * u⁻¹ * s⁻¹ ∈ U := by
      have := U.mul_mem hu h2
      simpa [mul_assoc] using this
    have hc : u * s * u⁻¹ * s⁻¹ = 1 := hUS _ hcU (S.mul_mem h1 (S.inv_mem hs))
    calc s * u = (u * s * u⁻¹ * s⁻¹)⁻¹ * (u * s) := by group
      _ = u * s := by rw [hc, inv_one, one_mul]
  · refine isUniqueMaxOver_iff.mpr ⟨⟨hlt, fun K hK hKU => ?_⟩, le_rfl, fun N hN hSN => ?_⟩
    · rcases hclaim K hK.le hKU with h | h
      · exact absurd h hK.ne'
      · exact h
    · rcases hclaim N hSN hN.1.le with h | h
      · exact h
      · exact absurd h hN.1.ne

private theorem mem_center_map_iff {Y : Type*} [Group Y] {L : Subgroup Y} {x : Y} :
    x ∈ (Subgroup.center ↥L).map L.subtype ↔ x ∈ L ∧ ∀ y ∈ L, x * y = y * x := by
  constructor
  · rintro ⟨⟨x, hx⟩, hz, rfl⟩
    refine ⟨hx, fun y hy => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2).symm, rfl⟩

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
private theorem normalizer_le_normalizer_of_char {S C : Subgroup X} (hCS : C ≤ S)
    (hC : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (C : Set X) := by
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := S)
    (C.subgroupOf S)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at this

private theorem isSolvable_sup_of_comm {G : Type*} [Group G] [Finite G] {U S : Subgroup G}
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hS : IsPGroup 2 S) : Group.IsSolvable ↥(U ⊔ S) := by
  set W := U ⊔ S with hW
  have hUW : U ≤ W := le_sup_left
  have hSW : S ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (U : Set G) := sup_le Subgroup.le_normalizer hSU
  haveI hN : (U.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW).mpr hWN
  haveI : Group.IsSolvable ↥(U.subgroupOf W) :=
    isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (hUc _ a.2 _ b.2))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (U.subgroupOf W)).comp (Subgroup.inclusion hSW)) := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf W) q
    have hw' : w ∈ (U : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left U S hSU]
      exact hw
    obtain ⟨u, hu, t, ht, rfl⟩ := hw'
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((⟨t, hSW ht⟩ : ↥W)⁻¹ * ⟨u * t, hw⟩ : ↥W) ∈ U.subgroupOf W
    rw [Subgroup.mem_subgroupOf]
    have hconj : t⁻¹ * u * t ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hSU (S.inv_mem ht)) u).mp hu
      simpa [mul_assoc] using this
    simpa [mul_assoc] using hconj
  haveI : Group.IsSolvable (↥W ⧸ U.subgroupOf W) := solvable_of_surjective hsurj
  exact solvable_of_ker_le_range (U.subgroupOf W).subtype (QuotientGroup.mk' (U.subgroupOf W))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

private theorem map_perfectCore_le' {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H : Subgroup G) : (perfectCore H).map f ≤ perfectCore (H.map f) :=
  le_iInf fun n => by
    rw [← map_derivedSeriesOf]
    exact Subgroup.map_mono (iInf_le _ n)

private theorem vZ_le_gnV (T H : Subgroup X) : VZ T H ≤ gnV T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨h, -, z, hz, rfl⟩
  exact (Subgroup.normalClosure_normal (s := (omegaOneCenterOf T : Set X))).conj_mem z
    (Subgroup.subset_normalClosure hz) h

theorem exists_central_elem_mem_gnA (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (hP : IsC118Pair T C₁ C₂) {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hLT : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center ↥L)) :
    ∃ z ∈ (Subgroup.center ↥L).map L.subtype, orderOf z = p ∧
      (z ∈ gnA T C₁ L ∨ z ∈ gnA T C₂ L) := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  set T' : Subgroup (X ⧸ gnC T) := gnImg T T with hT'
  set Zs : Subgroup (X ⧸ gnC T) := (Subgroup.center ↥L).map L.subtype with hZsdef
  have hTp : IsPGroup 2 T' := hX.sylow.2.1.map _
  have hZs : ∀ x, x ∈ Zs ↔ x ∈ L ∧ ∀ y ∈ L, x * y = y * x := fun x => mem_center_map_iff
  let Ω : Subgroup (X ⧸ gnC T) :=
    { carrier := {x | x ∈ Zs ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨Zs.mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := ((hZs x).1 hx.1).2 y ((hZs y).1 hy.1).1
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨Zs.one_mem, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨Zs.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hΩ : ∀ x, x ∈ Ω ↔ x ∈ Zs ∧ x ^ p = 1 := fun _ => Iff.rfl
  have hΩT : T' ≤ Subgroup.normalizer (Ω : Set (X ⧸ gnC T)) := by
    refine le_normalizer_of_conj_mem fun t ht x hx => ?_
    have htL : ∀ y ∈ L, t * y * t⁻¹ ∈ L := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (hLT ht) y).mp hy
    have htL' : ∀ y ∈ L, t⁻¹ * y * t ∈ L := fun y hy => by
      simpa using (Subgroup.mem_normalizer_iff.mp (hLT (T'.inv_mem ht)) y).mp hy
    obtain ⟨hxZ, hxp⟩ := hx
    obtain ⟨hxL, hxc⟩ := (hZs x).1 hxZ
    refine ⟨(hZs _).2 ⟨htL x hxL, fun y hy => ?_⟩, ?_⟩
    · have h := hxc (t⁻¹ * y * t) (htL' y hy)
      calc t * x * t⁻¹ * y = t * (x * (t⁻¹ * y * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * y * t) * x) * t⁻¹ := by rw [h]
        _ = y * (t * x * t⁻¹) := by group
    · rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  have hΩ0 : Ω ≠ ⊥ := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) p hpZ
    have h1 : orderOf ((x : ↥(Subgroup.center ↥L)) : ↥L) = p := (Subgroup.orderOf_coe x).trans hx
    have h2 : orderOf (((x : ↥(Subgroup.center ↥L)) : ↥L) : X ⧸ gnC T) = p :=
      (Subgroup.orderOf_coe _).trans h1
    have hyZ : (((x : ↥(Subgroup.center ↥L)) : ↥L) : X ⧸ gnC T) ∈ Zs :=
      ⟨(x : ↥L), x.2, rfl⟩
    have hyΩ : (((x : ↥(Subgroup.center ↥L)) : ↥L) : X ⧸ gnC T) ∈ Ω :=
      ⟨hyZ, by rw [← h2]; exact pow_orderOf_eq_one _⟩
    intro hΩ'
    rw [hΩ', Subgroup.mem_bot, ← orderOf_eq_one_iff, h2] at hyΩ
    exact hp.one_lt.ne' hyΩ
  obtain ⟨U, hUΩ, hU0, hTU, hUmin⟩ := exists_minimal_invariant hΩ0 hΩT
  have hUp : ∀ x ∈ U, x ^ p = 1 := fun x hx => ((hΩ x).1 (hUΩ hx)).2
  have hUZ : ∀ x ∈ U, x ∈ Zs := fun x hx => ((hΩ x).1 (hUΩ hx)).1
  have hUL : U ≤ L := fun x hx => ((hZs x).1 (hUZ x hx)).1
  have hUc : U ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (((hZs x).1 (hUZ x hx)).2 y hy).symm
  obtain ⟨⟨z₀, hz₀U⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU0
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hz₀ord : orderOf z₀ = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hUp z₀ hz₀U)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz₀1'
    · exact h
  have hz₀L : z₀ ∈ L := hUL hz₀U
  by_cases hc : U ≤ Subgroup.centralizer (T' : Set (X ⧸ gnC T))
  ·
    have hNT : Subgroup.normalizer (T' : Set (X ⧸ gnC T)) =
        gnImg T (Subgroup.normalizer (T : Set X)) :=
      normalizer_gnImg_eq hX le_rfl Subgroup.le_normalizer
        (fun R hTR hRT => by rw [le_antisymm hRT hTR])
    have hGN := isGNPair_of_isC118Pair hP
    have hN2 : Subgroup.normalizer (T : Set X) ≤ Subgroup.normalizer (C₂ : Set X) :=
      normalizer_le_normalizer_of_char hGN.le₂ hGN.char₂
    have hz₀N : z₀ ∈ Subgroup.normalizer (T' : Set (X ⧸ gnC T)) :=
      Subgroup.centralizer_le_normalizer _ (hc hz₀U)
    rw [hNT] at hz₀N
    exact ⟨z₀, hUZ z₀ hz₀U, hz₀ord, Or.inr ⟨Subgroup.map_mono hN2 hz₀N, hz₀L⟩⟩
  ·
    have hMP : MinParabolic (U ⊔ T') T' T' :=
      minParabolic_sup_of_minimal hp hp2 hTp hTU hUp hU0 hc hUmin
    obtain ⟨H₁, M₁, hmin, hF₁, hTH₁, hmap⟩ := Tits.GN516.exists_minParabolic_lift_of_le hX le_rfl
      inf_le_left (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow) hMP
    have hmap' : gnImg T H₁ = U ⊔ T' := hmap
    have hUH : U ≤ gnImg T H₁ := hmap' ▸ le_sup_left
    have hsolv : perfectCore H₁ ≤ Subgroup.centralizer (VZ T H₁ : Set X) := by
      have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
        ((hZs a).1 (hUZ a ha)).2 b (hUL hb)
      have hbot : perfectCore (U ⊔ T') = ⊥ :=
        (isSolvable_iff_perfectCore_eq_bot _).1 (isSolvable_sup_of_comm hTU hUc hTp)
      have hle : (perfectCore H₁).map π ≤ ⊥ := by
        have := map_perfectCore_le' π H₁
        rw [show H₁.map π = U ⊔ T' from hmap', hbot] at this
        exact this
      intro x hx
      have hxC : x ∈ gnC T := by
        have : π x = 1 := Subgroup.mem_bot.1 (hle ⟨x, hx, rfl⟩)
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact Subgroup.centralizer_le (vZ_le_gnV T H₁) hxC
    rcases concl_of_concl1Gen hF₁ hmin.isSylow (concl1Gen_of_perfectCore_le hP hmin hF₁ hsolv) with
      h1 | h2 | ⟨r, K, -, hKb, -, hres, -, -⟩
    · refine ⟨z₀, hUZ z₀ hz₀U, hz₀ord, Or.inl ⟨?_, hz₀L⟩⟩
      refine Subgroup.map_mono (Subgroup.centralizer_le_normalizer _) ?_
      refine Subgroup.map_mono (fun h hh => ?_) (hUH hz₀U)
      exact Subgroup.mem_centralizer_iff.2 fun c hc =>
        (Subgroup.mem_centralizer_iff.1 (h1 hc).2 h hh).symm
    · exact ⟨z₀, hUZ z₀ hz₀U, hz₀ord, Or.inr ⟨Subgroup.map_mono h2 (hUH hz₀U), hz₀L⟩⟩
    · exfalso
      have hYU : twoResidual (U ⊔ T') ≤ U := Tits.GN516.twoResidual_sup_le_of_pGroup hTp hTU
      have hUY : U ≤ twoResidual (U ⊔ T') := by
        intro u hu
        obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient (U ⊔ T') u (Subgroup.mem_sup_left hu)
        exact E1.mem_of_pow_mem_two_p hp hp2 (k := 1) (by simp [hUp u hu]) hj
      have hYimg : gnImg T (twoResidual H₁) = twoResidual (U ⊔ T') := by
        rw [gnImg, E1.map_twoResidual]
        exact congrArg twoResidual hmap'
      have hKsub : ∀ i, IsSubnormal (gnImg T (K i)) ⊤ := fun i =>
        isSubnormal_of_le_centralizer
          (((Subgroup.map_mono ((le_iSup K i).trans hres.ge)).trans hYimg.le).trans hYU)
          hUL hUc hL.2.1
      have hbot := Tits.GN516.twoResidual_gnImg_eq_bot_q hX
        ((B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans hTH₁)
        (fun i => ⟨(hKb i).1.1, (hKb i).1.2⟩) hres hKsub
      rw [hmap'] at hbot
      exact hU0 (le_bot_iff.1 (hUY.trans hbot.le))

end Centre

section Assembly

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem gnThree_gnCentre_of_cover (hG : KFactChevGenThree) (hGC : KFactChevGenCentre)
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (hP : IsC118Pair T C₁ C₂) {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T C₁ C₂ L)
    (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) (hcov : ParabolicCover T C₁ C₂ L) :
    (¬ pElementSubgroup 3 (gnA T C₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
      ¬ pElementSubgroup 3 (gnA T C₂ L) ≤ (Subgroup.center ↥L).map L.subtype) ∧
    (gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) → ∀ p : ℕ, p.Prime →
      p ∣ Nat.card (Subgroup.center ↥L) →
        1 < Open.pRank p (gnA T C₁ L) ∨ 1 < Open.pRank p (gnA T C₂ L)) := by
  refine ⟨gnThree_of_cover hG hX hY hcl hcov, fun hLT => ?_⟩
  have hodd := Tits.OrdinaryProofs.GNQuotient.not_two_dvd_card_center_of_isComponentOf
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.pCore_two_gnQuot hX) hY.1
  exact gnCentre_of_cover hGC hX hY hcl hcov hodd fun p hp hpZ =>
    exists_central_elem_mem_gnA hX hP hY.1 hLT hp (fun h => hodd (h ▸ hpZ)) hpZ

end Assembly

end CFSG.AGLEmbeddingD2.GN
