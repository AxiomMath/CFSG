module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open Subgroup

section ElemAbelian

variable {G : Type*} [Group G]

theorem i1020_isElemAbelian_closure {q : ℕ} {s : Set G}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hpow : ∀ a ∈ s, a ^ q = 1) :
    IsElemAbelian q (closure s) := by
  have hc : IsMulCommutative (closure s) :=
    isMulCommutative_closure fun a ha b hb _ => hcomm a ha b hb
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using closure_induction with
  | mem x hx => exact hpow x hx
  | one => exact one_pow q
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := setLike_mul_comm hx hy
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem i1020_isElemAbelian_sup {q : ℕ} {A B : Subgroup G} (hA : IsElemAbelian q A)
    (hB : IsElemAbelian q B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian q (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem i1020_isElemAbelian_zpowers {q : ℕ} {x : G} (hx : x ^ q = 1) :
    IsElemAbelian q (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem i1020_card_sup_zpowers [Finite G] {q : ℕ} (hq : q.Prime) {E : Subgroup G} {x : G}
    (hx : orderOf x = q) (hxE : x ∉ E) (hcomm : ∀ e ∈ E, e * x = x * e) :
    Nat.card (E ⊔ zpowers x : Subgroup G) = Nat.card E * q := by
  have hc : ∀ (a : E) (b : zpowers x), Commute (E.subtype a) ((zpowers x).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact Commute.zpow_right (hcomm a ha) k
  have hdisj : Disjoint E (zpowers x) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(E ⊓ zpowers x) ∣ q := by
      rw [← hx, ← Nat.card_zpowers]
      exact card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exact card_eq_one.1 h
    · exfalso
      have hle : zpowers x ≤ E ⊓ zpowers x := by
        refine (eq_of_le_of_card_ge inf_le_right ?_).ge
        rw [h, Nat.card_zpowers, hx]
      exact hxE (hle (mem_zpowers x)).1
  have hinj : Function.Injective (E.subtype.noncommCoprod (zpowers x).subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨E.subtype_injective, (zpowers x).subtype_injective, ?_⟩
    rwa [range_subtype, range_subtype]
  have hrange : (E.subtype.noncommCoprod (zpowers x).subtype hc).range = E ⊔ zpowers x := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
    Nat.card_zpowers, hx]

theorem i1020_adjoin [Finite G] {q : ℕ} (hq : q.Prime) {E : Subgroup G} (hE : IsElemAbelian q E)
    {m : ℕ} (hcard : Nat.card E = q ^ m) {x : G} (hx : orderOf x = q) (hxE : x ∉ E)
    (hcomm : ∀ e ∈ E, e * x = x * e) :
    IsElemAbelian q (E ⊔ zpowers x) ∧ Nat.card (E ⊔ zpowers x : Subgroup G) = q ^ (m + 1) := by
  refine ⟨i1020_isElemAbelian_sup hE (i1020_isElemAbelian_zpowers (hx ▸ pow_orderOf_eq_one x))
    ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hcomm a ha) k).eq
  · rw [i1020_card_sup_zpowers hq hx hxE hcomm, hcard, pow_succ]

theorem i1020_family [Finite G] {q : ℕ} {ι : Type*} [Fintype ι] (y : ι → G)
    (hy : ∀ i, orderOf (y i) = q) (hcomm : ∀ i j, i ≠ j → y i * y j = y j * y i)
    (hind : iSupIndep fun i => zpowers (y i)) :
    IsElemAbelian q (⨆ i, zpowers (y i)) ∧
      Nat.card (⨆ i, zpowers (y i) : Subgroup G) = q ^ Fintype.card ι := by
  have hc : Pairwise fun i j => ∀ a b : G, a ∈ zpowers (y i) → b ∈ zpowers (y j) →
      Commute a b := by
    intro i j hij a b ha hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hb
    exact Commute.zpow_zpow (hcomm i j hij) k l
  refine ⟨?_, ?_⟩
  · rw [iSup_eq_closure]
    refine i1020_isElemAbelian_closure ?_ ?_
    · intro a ha b hb
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
      by_cases hij : i = j
      · subst hij
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hj
        exact Commute.zpow_zpow_self (y i) k l
      · exact hc hij a b hi hj
    · intro a ha
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy i,
        pow_orderOf_eq_one, one_zpow]
  · have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hc) hind
    rw [← Subgroup.noncommPiCoprod_range (hcomm := hc),
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp [Nat.card_zpowers, hy]

theorem i1020_map_witness {G' : Type*} [Group G'] {q r : ℕ} (f : G →* G')
    (hf : Function.Injective f) {S E : Subgroup G} (hS : IsPGroup 2 S)
    (hES : E ≤ normalizer (S : Set G)) (hE : IsElemAbelian q E) (hEc : Nat.card E = q ^ r) :
    IsPGroup 2 (S.map f) ∧ (S ≠ ⊥ → S.map f ≠ ⊥) ∧ E.map f ≤ normalizer (S.map f : Set G') ∧
      IsElemAbelian q (E.map f) ∧ Nat.card (E.map f) = q ^ r :=
  ⟨hS.map f, fun h => (map_eq_bot_iff_of_injective S hf).not.2 h,
    (map_mono hES).trans (le_normalizer_map f), CFSG.SectionRank.isElemAbelian_map hE f,
    by rw [card_map_of_injective hf, hEc]⟩

end ElemAbelian

section Lifting

variable {G : Type*} [Group G]

theorem i1020_coprime_lift [Finite G] {G' : Type*} [Group G'] {p : ℕ} [hp : Fact p.Prime]
    (π : G →* G') (A : Subgroup G) (hA : ¬ p ∣ Nat.card (A ⊓ π.ker : Subgroup G))
    {E' : Subgroup G'} (hE'A : E' ≤ A.map π) (hE' : IsElemAbelian p E') {k : ℕ}
    (hk : Nat.card E' = p ^ k) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  set P : Subgroup G := A ⊓ E'.comap π with hPdef
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p P))
  set E : Subgroup G := (Q : Subgroup P).map P.subtype with hEdef
  have hEP : E ≤ P := map_subtype_le _
  set f : P →* G' := π.comp P.subtype with hf
  have hrange : f.range = E' := by
    rw [hf, MonoidHom.range_comp, range_subtype]
    apply le_antisymm
    · rw [map_le_iff_le_comap]; exact inf_le_right
    · intro e he
      obtain ⟨a, ha, rfl⟩ := mem_map.1 (hE'A he)
      exact ⟨a, ⟨ha, he⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card (A ⊓ π.ker : Subgroup G) := by
    have h1 : f.ker = (A ⊓ π.ker).subgroupOf P := by
      ext x
      simp only [hf, MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype, mem_subgroupOf,
        mem_inf]
      exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
    have h2 : A ⊓ π.ker ≤ P := by
      intro x hx
      refine mem_inf.2 ⟨(mem_inf.1 hx).1, ?_⟩
      rw [mem_comap, MonoidHom.mem_ker.1 (mem_inf.1 hx).2]
      exact one_mem _
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe h2).toEquiv
  have hPcard : Nat.card P = Nat.card (A ⊓ π.ker : Subgroup G) * p ^ k := by
    rw [← card_mul_index f.ker, index_ker, hrange, hker, hk]
  have hc0 : Nat.card (A ⊓ π.ker : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hEcard : Nat.card E = p ^ k := by
    rw [hEdef, card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity, hPcard,
      Nat.factorization_mul hc0 (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hA, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  have hcop : Nat.Coprime (p ^ k) (Nat.card (A ⊓ π.ker : Subgroup G)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hA)
  have hdisj : ∀ x ∈ E, π x = 1 → x = 1 := by
    intro x hx hπx
    have h1 : Nat.card (E ⊓ π.ker : Subgroup G) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
      · rw [← hEcard]; exact card_dvd_of_le inf_le_left
      · exact card_dvd_of_le (inf_le_inf_right _ (hEP.trans inf_le_left))
    have h2 : x ∈ E ⊓ π.ker := ⟨hx, hπx⟩
    rw [card_eq_one.1 h1] at h2
    exact h2
  have hmemE' : ∀ x ∈ E, π x ∈ E' := fun x hx => (hEP hx).2
  have := hE'.1
  refine ⟨E, hEP.trans inf_le_left, ⟨?_, fun x hx => ?_⟩, hEcard⟩
  · rw [← le_centralizer_iff_isMulCommutative]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    have h1 : π (b * a * b⁻¹ * a⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        setLike_mul_comm (hmemE' b hb) (hmemE' a ha)]
      group
    have h2 := hdisj _ (E.mul_mem (E.mul_mem (E.mul_mem hb ha) (E.inv_mem hb)) (E.inv_mem ha)) h1
    calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
      _ = a * b := by rw [h2, one_mul]
  · exact hdisj _ (E.pow_mem hx p) (by rw [map_pow, hE'.2 _ (hmemE' x hx)])

theorem i1020_frattini_conj [Finite G] {p : ℕ} [Fact p.Prime] {P S : Subgroup G} (hSP : S ≤ P)
    (hS : Nat.card S = p ^ (Nat.card P).factorization p) {g : G}
    (hg : g ∈ normalizer (P : Set G)) :
    ∃ h ∈ P, h⁻¹ * g ∈ normalizer (S : Set G) := by
  set S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom with hS'def
  have hS'P : S' ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.1 hg s).1 (hSP hs)
  have hS'card : Nat.card S' = Nat.card S := card_map_of_injective (MulAut.conj g).injective
  let Q₁ : Sylow p P := Sylow.ofCard (S.subgroupOf P) (by
    rw [← hS]; exact Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv)
  let Q₂ : Sylow p P := Sylow.ofCard (S'.subgroupOf P) (by
    rw [← hS, ← hS'card]; exact Nat.card_congr (subgroupOfEquivOfLe hS'P).toEquiv)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq P Q₁ Q₂
  have key : ∀ y ∈ P, g⁻¹ * y * g ∈ S ↔ (h : G)⁻¹ * y * h ∈ S := by
    intro y hy
    have h1 : (⟨y, hy⟩ : P) ∈ (Q₂ : Subgroup P) ↔ (⟨y, hy⟩ : P) ∈ (Q₁ : Subgroup P).map
        (MulAut.conj h).toMonoidHom := by
      rw [← hh, Sylow.coe_subgroup_smul, pointwise_smul_def]
      rfl
    have h2 : (⟨y, hy⟩ : P) ∈ (Q₂ : Subgroup P) ↔ g⁻¹ * y * g ∈ S := by
      show (⟨y, hy⟩ : P) ∈ S'.subgroupOf P ↔ _
      rw [mem_subgroupOf, hS'def, mem_map_equiv, MulAut.conj_symm_apply]
    have h3 : (⟨y, hy⟩ : P) ∈ (Q₁ : Subgroup P).map (MulAut.conj h).toMonoidHom ↔
        (h : G)⁻¹ * y * h ∈ S := by
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      show _ ∈ S.subgroupOf P ↔ _
      rw [mem_subgroupOf]
      rfl
    rw [← h2, h1, h3]
  have hhP : (h : G) ∈ normalizer (P : Set G) := le_normalizer h.2
  have hc : (h : G)⁻¹ * g ∈ normalizer (P : Set G) := mul_mem (inv_mem hhP) hg
  refine ⟨h, h.2, ?_⟩
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have hy : g * s * g⁻¹ ∈ P := (mem_normalizer_iff.1 hg s).1 (hSP hs)
    have := (key _ hy).1 (by simpa [mul_assoc] using hs)
    simpa [mul_assoc] using this
  · intro hs
    have hsP : s ∈ P := (mem_normalizer_iff.1 hc s).2 (hSP hs)
    have hy : g * s * g⁻¹ ∈ P := (mem_normalizer_iff.1 hg s).1 hsP
    have := (key _ hy).2 (by simpa [mul_assoc] using hs)
    simpa [mul_assoc] using this

theorem i1020_frattini_lift [Finite G] {G' : Type*} [Group G'] {p : ℕ} [Fact p.Prime]
    (π : G →* G') (hπ : Function.Surjective π) {S' : Subgroup G'} (hS' : IsPGroup p S') :
    ∃ S : Subgroup G, IsPGroup p S ∧ S.map π = S' ∧
      normalizer (S' : Set G') ≤ (normalizer (S : Set G)).map π := by
  set P : Subgroup G := S'.comap π with hPdef
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p P))
  set S : Subgroup G := (Q : Subgroup P).map P.subtype with hSdef
  have hSP : S ≤ P := map_subtype_le _
  have hScard : Nat.card S = p ^ (Nat.card P).factorization p := by
    rw [hSdef, card_map_of_injective P.subtype_injective]; exact Q.card_eq_multiplicity
  have hSmap : S.map π = S' := by
    apply le_antisymm
    · rw [map_le_iff_le_comap]; exact hSP
    · let πP : P →* S' := (π.comp P.subtype).codRestrict S' (fun x => x.2)
      have hπP : Function.Surjective πP := by
        rintro ⟨s, hs⟩
        obtain ⟨x, rfl⟩ := hπ s
        exact ⟨⟨x, hs⟩, rfl⟩
      have htop : ((Q.mapSurjective hπP : Sylow p S') : Subgroup S') = ⊤ :=
        ((Q.mapSurjective hπP).is_maximal' (hS'.of_equiv topEquiv.symm) le_top).symm
      intro s hs
      have hmem : (⟨s, hs⟩ : S') ∈ ((Q.mapSurjective hπP : Sylow p S') : Subgroup S') := by
        rw [htop]; exact mem_top _
      rw [Sylow.coe_mapSurjective, mem_map] at hmem
      obtain ⟨x, hx, hxs⟩ := hmem
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxs⟩
  refine ⟨S, Q.isPGroup'.map _, hSmap, ?_⟩
  intro g' hg'
  obtain ⟨g, rfl⟩ := hπ g'
  have hgP : g ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    simp only [hPdef, mem_comap, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hg') (π x)
  obtain ⟨h, hhP, hhg⟩ := i1020_frattini_conj hSP hScard hgP
  have hπh : π h ∈ S.map π := by rw [hSmap]; exact hhP
  obtain ⟨s, hs, hsh⟩ := mem_map.1 hπh
  refine ⟨s * (h⁻¹ * g), mul_mem (le_normalizer hs) hhg, ?_⟩
  rw [map_mul, hsh, map_mul, map_inv, mul_inv_cancel_left]

end Lifting

section DirectPower

theorem i1020_exists_not_comm {K : Type*} [Group K] [IsSimpleGroup K]
    (hnc : ∃ a b : K, a * b ≠ b * a) {x : K} (hx : x ≠ 1) : ∃ b : K, b * x ≠ x * b := by
  by_contra h
  push Not at h
  have hcen : center K ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnc
    have : b ∈ center K := htop ▸ mem_top b
    exact hab (mem_center_iff.1 this a)
  have hbot : center K = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right hcen
  have hxc : x ∈ center K := mem_center_iff.2 h
  rw [hbot, mem_bot] at hxc
  exact hx hxc

theorem i1020_exists_mulSingle_mem {K : Type*} [Group K] [IsSimpleGroup K]
    (hnc : ∃ a b : K, a * b ≠ b * a) {ι : Type*} [DecidableEq ι] {N : Subgroup (ι → K)}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : ∃ i, ∀ a : K, Pi.mulSingle i a ∈ N := by
  obtain ⟨⟨f, hfN⟩, hf1⟩ := (ne_bot_iff_exists_ne_one).1 hN1
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 1 := by
    by_contra h
    push Not at h
    exact hf1' (funext h)
  obtain ⟨b, hb⟩ := i1020_exists_not_comm hnc hi
  refine ⟨i, ?_⟩
  set M : Subgroup K := N.comap (MonoidHom.mulSingle (fun _ => K) i) with hMdef
  have hM : M.Normal := by
    constructor
    intro a ha c
    rw [hMdef, mem_comap] at ha ⊢
    have := hN.conj_mem _ ha (Pi.mulSingle i c)
    simpa [Pi.mulSingle_mul, Pi.mulSingle_inv] using this
  have hc : Pi.mulSingle i (b * f i * b⁻¹ * (f i)⁻¹) ∈ N := by
    have h1 : Pi.mulSingle i b * f * (Pi.mulSingle i b)⁻¹ * f⁻¹ ∈ N :=
      N.mul_mem (hN.conj_mem f hfN _) (N.inv_mem hfN)
    have h2 : Pi.mulSingle i b * f * (Pi.mulSingle i b)⁻¹ * f⁻¹ =
        Pi.mulSingle i (b * f i * b⁻¹ * (f i)⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rwa [h2] at h1
  have hMne : M ≠ ⊥ := by
    intro hbot
    have : b * f i * b⁻¹ * (f i)⁻¹ ∈ M := hc
    rw [hbot, mem_bot] at this
    apply hb
    calc b * f i = (b * f i * b⁻¹ * (f i)⁻¹) * (f i * b) := by group
      _ = f i * b := by rw [this, one_mul]
  have hMtop : M = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal M).resolve_left hMne
  intro a
  have : a ∈ M := hMtop ▸ mem_top a
  exact this

end DirectPower

end CFSG.HardMathSupport.Solomon.Coordinator
