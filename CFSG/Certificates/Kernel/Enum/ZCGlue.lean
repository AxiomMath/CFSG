module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCSound
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

variable {n w : Nat}

theorem wperm_prep {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n ≤ 2 ^ w) (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb)
    (hbi : PRep n w bi gb⁻¹) :
    ∃ g ∈ Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))),
      PRep n w (wperm n w (mask w) a b ai bi W len) g := by
  classical
  set H := Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n)))
  have hga : ga ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgb : gb ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hlt : ∀ c, ∃ g ∈ H, ∀ q (hq : q < n),
      CFSG.KC.Enum.lt w (mask w) a b ai bi c q = (g ⟨q, hq⟩ : Nat) := by
    intro c
    unfold CFSG.KC.Enum.lt
    simp only [PK.nIf_eq]
    by_cases h0 : Nat.beq c 0 = true
    · exact ⟨ga, hga, fun q hq => by rw [if_pos h0]; exact ha ⟨q, hq⟩⟩
    by_cases h1 : Nat.beq c 1 = true
    · exact ⟨gb, hgb, fun q hq => by rw [if_neg h0, if_pos h1]; exact hb ⟨q, hq⟩⟩
    by_cases h2 : Nat.beq c 2 = true
    · exact ⟨ga⁻¹, H.inv_mem hga, fun q hq => by
        rw [if_neg h0, if_neg h1, if_pos h2]; exact hai ⟨q, hq⟩⟩
    · exact ⟨gb⁻¹, H.inv_mem hgb, fun q hq => by
        rw [if_neg h0, if_neg h1, if_neg h2]; exact hbi ⟨q, hq⟩⟩
  have hfold : ∀ k, ∃ g ∈ H, ∀ q (hq : q < n),
      foldN k (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q =
        (g ⟨q, hq⟩ : Nat) := by
    intro k
    induction k with
    | zero => exact ⟨1, H.one_mem, fun q hq => by rw [PK.foldN_eq]; rfl⟩
    | succ k ih =>
      obtain ⟨g, hg, hk⟩ := ih
      obtain ⟨gl, hgl, hl⟩ := hlt (wl W k)
      refine ⟨g * gl, H.mul_mem hg hgl, fun q hq => ?_⟩
      have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
        fun f s => by
          rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
            List.foldr_nil]
      rw [e, hl q hq, hk _ (gl ⟨q, hq⟩).2]
      rfl
  obtain ⟨g, hg, hf⟩ := hfold len
  refine ⟨g, hg, fun x => ?_⟩
  set F : Nat → Nat := fun p =>
    foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) p
  have hF : ∀ y < n, F y < 2 ^ w := fun y hy => by
    change foldN len _ y < 2 ^ w
    rw [hf y hy]
    exact Nat.lt_of_lt_of_le (g ⟨y, hy⟩).2 hw
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w F hF (clog n) 0
  have e : wperm n w (mask w) a b ai bi W len = pmkT n w F (clog n) 0 := by
    unfold wperm pmk
    rw [PF.strictN_eqP]
  have hx : (x : Nat) < 2 ^ clog n := Nat.lt_of_lt_of_le x.2 hc
  rw [e, PF.pg_of_fld h (by simp only [hx, ↓reduceIte, Nat.zero_add, x.2]; exact hF x x.2)]
  simp only [hx, ↓reduceIte, Nat.zero_add, x.2]
  exact hf x x.2

theorem conj_inv_mem_of_finite {A : Type} [Group A] {O : Set A} (hO : O.Finite) {g : A}
    (h : ∀ x ∈ O, g * x * g⁻¹ ∈ O) : ∀ x ∈ O, g⁻¹ * x * g⁻¹⁻¹ ∈ O := by
  have hm : Set.MapsTo (fun x => g * x * g⁻¹) O O := fun x hx => h x hx
  have hb := (hO.injOn_iff_bijOn_of_mapsTo hm).mp
    (fun x _ y _ hxy => mul_left_cancel (mul_right_cancel hxy))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hb.surjOn hx
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rw [e]
  exact hy

theorem zcw_of_lists {A : Type} [Group A] [Finite A] {ga gb z : A} {p k nL nS kg : Nat}
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card (Subgroup.closure ({ga, gb} : Set A)))
    (hz : z ∈ Subgroup.closure ({ga, gb} : Set A)) (hzo : orderOf z = p) {U : Nat → A}
    (hUa : ∀ i < nL, ∃ j < nL, U j = ga * U i * ga⁻¹)
    (hUb : ∀ i < nL, ∃ j < nL, U j = gb * U i * gb⁻¹)
    (hW : ∀ i < nL, ∃ e : Nat, ∃ j < nL, U j = z ^ e * U i * (z ^ e)⁻¹ ∧ U i * U j ≠ U j * U i)
    {gG : Nat → A} (hG : ∀ j < kg, gG j ∈ Subgroup.closure ({ga, gb} : Set A)) {Ev : Nat → A}
    (hnS : nS = 2 ^ k) (hEv : ∀ i < nS, Ev i ∈ Subgroup.closure {x | ∃ j < kg, x = gG j})
    (hmul : ∀ i < nS, ∀ j < kg, ∃ R < nS, Ev R = Ev i * gG j)
    (hinj : ∀ i < nS, ∀ i' < nS, Ev i = Ev i' → i = i')
    (hinv : ∀ i < nS, Ev i * Ev i = 1 → Ev i ≠ 1 → ∃ ix < nL, U ix = Ev i) :
    ZCW ↥(Subgroup.closure ({ga, gb} : Set A)) p := by
  classical
  set M := Subgroup.closure ({ga, gb} : Set A)
  set S := Subgroup.closure {x | ∃ j < kg, x = gG j}
  set E : Set A := Set.range (fun i : Fin nS => Ev i)
  have hEm : ∀ x ∈ E, ∀ j < kg, x * gG j ∈ E := by
    rintro _ ⟨i, rfl⟩ j hj
    obtain ⟨R, hR, e⟩ := hmul i i.2 j hj
    exact ⟨⟨R, hR⟩, e⟩
  have key : ∀ g ∈ S, ∀ x ∈ E, x * g ∈ E := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨j, hj, rfl⟩ := hs
      exact fun x hx => hEm x hx j hj
    | one => exact fun x hx => by simpa using hx
    | mul g h _ _ hg hh => exact fun x hx => by simpa [mul_assoc] using hh _ (hg x hx)
    | inv g _ hg => exact zc_mul_inv_mem_of_finite hg
  have hnS0 : 0 < nS := hnS ▸ Nat.two_pow_pos k
  have h1E : (1 : A) ∈ E := by
    have h0 : Ev 0 ∈ E := ⟨⟨0, hnS0⟩, rfl⟩
    simpa using key _ (S.inv_mem (hEv 0 hnS0)) _ h0
  have hSE : ∀ x, x ∈ S ↔ x ∈ E := fun x =>
    ⟨fun hx => by simpa using key x hx 1 h1E, by rintro ⟨i, rfl⟩; exact hEv i i.2⟩
  have hcardS : Nat.card S = nS := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hSE),
      Nat.card_range_of_injective (fun i i' e => Fin.ext (hinj i i.2 i' i'.2 e)), Nat.card_fin]
  have hSM : S ≤ M := (Subgroup.closure_le _).mpr (by rintro x ⟨j, hj, rfl⟩; exact hG j hj)
  have hS' : Nat.card (S.subgroupOf M) = 2 ^ k := by
    rw [← hnS, ← hcardS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  set O : Set A := Set.range (fun i : Fin nL => U i)
  have hOfin : O.Finite := Set.finite_range _
  have hOa : ∀ x ∈ O, ga * x * ga⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUa i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hOb : ∀ x ∈ O, gb * x * gb⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUb i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hO' : ∀ x ∈ List.ofFn (fun i : Fin nL => U i), ∀ g ∈ [ga, gb, ga⁻¹, gb⁻¹],
      g * x * g⁻¹ ∈ List.ofFn (fun i : Fin nL => U i) := by
    intro x hx g hg
    rw [List.mem_ofFn] at hx ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact hOa x hx
    · exact hOb x hx
    · exact conj_inv_mem_of_finite hOfin hOa x hx
    · exact conj_inv_mem_of_finite hOfin hOb x hx
  have hOconj := zc_conj_mem_of_closure hO'
  unfold ZCW
  refine ⟨⟨z, hz⟩, by rw [← Subgroup.orderOf_coe]; exact hzo, fun u hu hu1 => Or.inl ?_⟩
  obtain ⟨g, hg⟩ := zc_exists_conj_mem_of_card (S.subgroupOf M) k hS' hk hu
  have hgS : (g : A) * u * (g : A)⁻¹ ∈ S := by simpa using Subgroup.mem_subgroupOf.mp hg
  obtain ⟨⟨i, hi⟩, hie⟩ := (hSE _).mp hgS
  have hie' : Ev i = (g : A) * u * (g : A)⁻¹ := hie
  have hu' : (u : A) * u = 1 := by simpa using congrArg Subtype.val hu
  have hss : Ev i * Ev i = 1 := by
    rw [hie']
    have e : (g : A) * u * (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) =
        (g : A) * ((u : A) * u) * (g : A)⁻¹ := by group
    rw [e, hu', mul_one, mul_inv_cancel]
  have hs1 : Ev i ≠ 1 := by
    rw [hie']
    intro e
    apply hu1
    apply Subtype.ext
    have e2 : (u : A) = (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) * g := by group
    rw [e2, e]
    simp
  obtain ⟨ix, hix, hUix⟩ := hinv i hi hss hs1
  have hmemO : (u : A) ∈ List.ofFn (fun i : Fin nL => U i) := by
    have h := hOconj ((g : A)⁻¹) (M.inv_mem g.2) (U ix) (List.mem_ofFn.2 ⟨⟨ix, hix⟩, rfl⟩)
    have e : (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) * (g : A)⁻¹⁻¹ = u := by group
    rwa [hUix, hie', e] at h
  obtain ⟨⟨i', hi'⟩, hi'e⟩ := List.mem_ofFn.1 hmemO
  have hi'e' : U i' = u := hi'e
  obtain ⟨e, j, hj, hUj, hne⟩ := hW i' hi'
  refine ⟨1, Subgroup.one_mem _, ⟨z, hz⟩ ^ e, pow_mem (Subgroup.mem_zpowers _) e,
    fun heq => hne ?_⟩
  have h2 := congrArg Subtype.val heq
  simp only [one_mul, inv_one, mul_one, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow,
    Subgroup.coe_mk] at h2
  rw [hUj, hi'e']
  exact h2

end CFSG.KC.EnumSound

end
