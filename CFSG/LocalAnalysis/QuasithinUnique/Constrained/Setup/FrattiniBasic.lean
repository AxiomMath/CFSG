module

public import Mathlib.GroupTheory.Frattini
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup

theorem isCoatom_map_of_ker_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {M : Subgroup G} (hM : IsCoatom M) (hk : f.ker ≤ M) :
    IsCoatom (M.map f) := by
  refine ⟨fun h => ?_, fun N hN => ?_⟩
  · apply hM.1
    have := congrArg (Subgroup.comap f) h
    rwa [comap_map_eq_self hk, comap_top] at this
  · have h1 : M < N.comap f := by
      refine lt_of_le_of_ne (by rw [← comap_map_eq_self hk]; exact Subgroup.comap_mono hN.le) ?_
      intro heq
      have := congrArg (Subgroup.map f) heq
      rw [map_comap_eq_self_of_surjective hf] at this
      exact hN.ne this
    have h2 := hM.2 _ h1
    have := congrArg (Subgroup.map f) h2
    rwa [map_comap_eq_self_of_surjective hf, Subgroup.map_top, f.range_eq_top.mpr hf] at this

theorem frattini_quotient_eq (G : Type*) [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (hA : A ≤ frattini G) :
    frattini (G ⧸ A) = (frattini G).map (QuotientGroup.mk' A) := by
  apply le_antisymm
  · have hsurj := QuotientGroup.mk'_surjective A
    have h1 : (frattini (G ⧸ A)).comap (QuotientGroup.mk' A) ≤ frattini G := by
      unfold frattini Order.radical
      refine le_iInf₂ fun M hM => ?_
      have hkM : (QuotientGroup.mk' A).ker ≤ M := by
        rw [QuotientGroup.ker_mk']
        exact hA.trans (frattini_le_coatom hM)
      have hc := isCoatom_map_of_ker_le _ hsurj hM hkM
      calc (frattini (G ⧸ A)).comap (QuotientGroup.mk' A)
          ≤ (M.map (QuotientGroup.mk' A)).comap (QuotientGroup.mk' A) :=
            Subgroup.comap_mono (frattini_le_coatom hc)
        _ = M := comap_map_eq_self hkM
    calc frattini (G ⧸ A)
        = ((frattini (G ⧸ A)).comap (QuotientGroup.mk' A)).map (QuotientGroup.mk' A) :=
          (map_comap_eq_self_of_surjective hsurj _).symm
      _ ≤ _ := Subgroup.map_mono h1
  · have := frattini_le_comap_frattini_of_surjective (φ := QuotientGroup.mk' A)
      (QuotientGroup.mk'_surjective A)
    exact Subgroup.map_le_iff_le_comap.mpr this

theorem frattini_quotient_frattini (G : Type*) [Group G] [Finite G] :
    frattini (G ⧸ frattini G) = ⊥ := by
  rw [frattini_quotient_eq G (frattini G) le_rfl]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem frattini_sylow_normal (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p (frattini G)) : (P.map (frattini G).subtype).Normal := by
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  have normalizer_P := frattini_nongenerating frattini_argument
  exact normalizer_eq_top_iff.mp normalizer_P

theorem frattini_le_frattini_of_normal (G : Type*) [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] : (frattini N).map N.subtype ≤ frattini G := by
  have hnorm : ((frattini N).map N.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  unfold frattini Order.radical
  refine le_iInf₂ fun M hM => ?_
  by_contra hnle
  have h1 : M ⊔ (frattini N).map N.subtype = ⊤ := by
    have hlt : M < M ⊔ (frattini N).map N.subtype :=
      lt_of_le_of_ne le_sup_left (fun h => hnle (h ▸ le_sup_right))
    exact hM.2 _ hlt
  have h2 : (M ⊓ N).subgroupOf N ⊔ frattini N = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx' : (x : G) ∈ M ⊔ (frattini N).map N.subtype := h1 ▸ mem_top _
    obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    obtain ⟨n', hn', rfl⟩ := hn
    have hmN : m ∈ N := by
      have : m = (x : G) * (n' : G)⁻¹ := by rw [← hmn]; simp
      rw [this]
      exact mul_mem x.2 (inv_mem n'.2)
    have hxe : x = ⟨m, hmN⟩ * n' := by
      apply Subtype.ext
      simpa using hmn.symm
    rw [hxe]
    exact mul_mem (mem_sup_left (by exact ⟨hm, hmN⟩)) (mem_sup_right hn')
  have h3 := frattini_nongenerating h2
  apply hnle
  intro y hy
  obtain ⟨y', -, rfl⟩ := hy
  have : y' ∈ (M ⊓ N).subgroupOf N := h3 ▸ mem_top _
  exact (mem_inf.mp this).1

theorem frattini_finite_properties (G : Type*) [Group G] [Finite G] :
    (frattini G).Characteristic ∧
    (∀ (p : ℕ) [Fact p.Prime] (P : Sylow p (frattini G)),
      (P.map (frattini G).subtype).Normal) ∧
    (∀ (N : Subgroup G) [N.Normal], (frattini N).map N.subtype ≤ frattini G) ∧
    (∀ (A : Subgroup G) [A.Normal], A ≤ frattini G →
      frattini (G ⧸ A) = (frattini G).map (QuotientGroup.mk' A)) ∧
    frattini (G ⧸ frattini G) = ⊥ :=
  ⟨inferInstance, fun p _ P => frattini_sylow_normal G p P,
    fun N _ => frattini_le_frattini_of_normal G N,
    fun A _ hAΦ => frattini_quotient_eq G A hAΦ, frattini_quotient_frattini G⟩

theorem frattini_map_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (frattini X).map e.toMonoidHom = frattini Y := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro y hy
    have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hy
    exact ⟨e.symm y, h, by simp⟩

theorem exists_complement_of_frattini_eq_bot {N : Type*} [Group N] [Finite N]
    (hΦ : frattini N = ⊥) (V : Subgroup N) [V.Normal] [IsMulCommutative V] :
    ∃ U : Subgroup N, V ⊓ U = ⊥ ∧ V ⊔ U = ⊤ := by
  obtain ⟨U, hU, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup N))
    {U : Subgroup N | V ⊔ U = ⊤} ⟨⊤, by simp⟩
  refine ⟨U, ?_, hU⟩
  by_contra hne
  set D : Subgroup N := V ⊓ U with hD
  have hDn : D.Normal := by
    refine ⟨fun d hd n => ?_⟩
    have hn : n ∈ V ⊔ U := hU ▸ mem_top n
    obtain ⟨v, hv, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hn
    have h1 : u * d * u⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem d hd.1 u
    have h2 : u * d * u⁻¹ ∈ U := mul_mem (mul_mem hu hd.2) (inv_mem hu)
    have hd' : u * d * u⁻¹ ∈ D := ⟨h1, h2⟩
    have hcomm : v * (u * d * u⁻¹) = (u * d * u⁻¹) * v := by
      have := (inferInstance : IsMulCommutative V).is_comm.comm ⟨v, hv⟩ ⟨u * d * u⁻¹, h1⟩
      exact congrArg Subtype.val this
    have : v * u * d * (v * u)⁻¹ = u * d * u⁻¹ := by
      calc v * u * d * (v * u)⁻¹ = v * (u * d * u⁻¹) * v⁻¹ := by group
        _ = (u * d * u⁻¹) * v * v⁻¹ := by rw [hcomm]
        _ = u * d * u⁻¹ := by group
    rw [this]
    exact hd'
  have hDbot : D ≠ ⊥ := hne
  obtain ⟨M, hM, hDM⟩ : ∃ M : Subgroup N, IsCoatom M ∧ ¬ D ≤ M := by
    by_contra hall
    push Not at hall
    apply hDbot
    rw [eq_bot_iff, ← hΦ]
    unfold frattini Order.radical
    exact le_iInf₂ fun M hM => hall M hM
  have hMD : M ⊔ D = ⊤ := by
    have hlt : M < M ⊔ D := lt_of_le_of_ne le_sup_left (fun h => hDM (h ▸ le_sup_right))
    exact hM.2 _ hlt
  have hU' : V ⊔ (U ⊓ M) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ V ⊔ U := hU ▸ mem_top x
    obtain ⟨v, hv, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hu' : u ∈ M ⊔ D := hMD ▸ mem_top u
    obtain ⟨m, hm, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu'
    have hmU : m ∈ U := by
      have : m = (m * d) * d⁻¹ := by group
      rw [this]
      exact mul_mem hu (inv_mem hd.2)
    have hv' : m * d * m⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem d hd.1 m
    have : v * (m * d) = (v * (m * d * m⁻¹)) * m := by group
    rw [this]
    exact mul_mem (mem_sup_left (mul_mem hv hv')) (mem_sup_right ⟨hmU, hm⟩)
  have hlt : U ⊓ M < U := by
    refine lt_of_le_of_ne inf_le_left fun h => hDM ?_
    have hUM : U ≤ M := by
      intro y hy
      have : y ∈ U ⊓ M := by rw [h]; exact hy
      exact this.2
    exact inf_le_right.trans hUM
  exact hmin _ hU' hlt


theorem eq_bot_of_frattini_of_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) (hΦN : frattini N = ⊥) (hN : ∃ m : ℕ, N.index = p ^ m)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] (hVΦ : V ≤ frattini G) (hVN : V ≤ N)
    (hVp : ¬ p ∣ Nat.card V) : V = ⊥ := by
  have hVn : (V.subgroupOf N).Normal := ⟨fun v hv n => by
    have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    exact Subgroup.mem_subgroupOf.mpr ((inferInstance : V.Normal).conj_mem v hv' n)⟩
  have hVc : IsMulCommutative (V.subgroupOf N) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h := (inferInstance : IsMulCommutative V).is_comm.comm
      ⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩ ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩
    have h2 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h2)
  obtain ⟨U, hUinf, hUsup⟩ := exists_complement_of_frattini_eq_bot hΦN (V.subgroupOf N)
  have hVmap : (V.subgroupOf N).map N.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVN
  have hinf : V ⊓ U.map N.subtype = ⊥ := by
    rw [← hVmap, ← Subgroup.map_inf_eq _ _ _ N.subtype_injective, hUinf, Subgroup.map_bot]
  have hsup : V ⊔ U.map N.subtype = N := by
    rw [← hVmap, ← Subgroup.map_sup, hUsup, Subgroup.map_top, Subgroup.range_subtype]
  have hcop : Nat.Coprime N.index (Nat.card V) := by
    obtain ⟨m, hm⟩ := hN
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hVp)
  obtain ⟨D, -, hVD, hVDt⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V N (U.map N.subtype)
      hcop hinf hsup
  have hDtop : D = ⊤ := by
    apply frattini_nongenerating
    refine eq_top_iff.mpr ?_
    rw [← hVDt]
    exact sup_le (hVΦ.trans le_sup_right) le_sup_left
  rw [← hVD, hDtop, inf_top_eq]

theorem frattini_eq_of_pCore_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hO : CFSG.pCore p G = ⊥) (N : Subgroup G) [N.Normal] (hN : IsPGroup p (G ⧸ N)) :
    (frattini N).map N.subtype = frattini G := by
  classical
  set A : Subgroup G := (frattini N).map N.subtype with hA
  have hAΦ : A ≤ frattini G := frattini_le_frattini_of_normal G N
  have hAn : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hpΦ : ¬ p ∣ Nat.card (frattini G) := by
    intro hdvd
    obtain ⟨P⟩ : Nonempty (Sylow p (frattini G)) := inferInstance
    have hPn := frattini_sylow_normal G p P
    have hP2 : P.map (frattini G).subtype ≤ CFSG.pCore p G :=
      le_sSup ⟨hPn, (P.isPGroup').map (frattini G).subtype⟩
    rw [hO, le_bot_iff] at hP2
    have hcard : Nat.card P = 1 := by
      have : Nat.card (P.map (frattini G).subtype) = Nat.card P :=
        Nat.card_congr
          (Subgroup.equivMapOfInjective _ _ (frattini G).subtype_injective).toEquiv.symm
      rw [← this, hP2]; exact Subgroup.card_bot
    rw [Sylow.card_eq_multiplicity] at hcard
    have : 0 < (Nat.card (frattini G)).factorization p :=
      (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd)
    have h1 : 1 < p ^ (Nat.card (frattini G)).factorization p :=
      Nat.one_lt_pow this.ne' (Fact.out : p.Prime).one_lt
    omega
  have hΦN : frattini G ≤ N := by
    intro φ hφ
    have hord : ¬ p ∣ orderOf φ := by
      intro h
      apply hpΦ
      refine h.trans ?_
      have := Subgroup.orderOf_dvd_natCard (frattini G) hφ
      simpa [Subgroup.orderOf_mk] using this
    obtain ⟨k, hk⟩ := hN (QuotientGroup.mk φ)
    have h1 : orderOf (QuotientGroup.mk (s := N) φ) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk (s := N) φ) ∣ orderOf φ := by
      have := orderOf_map_dvd (QuotientGroup.mk' N) φ
      simpa using this
    have hcop : Nat.Coprime (orderOf φ) (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hord).symm
    have h3 : orderOf (QuotientGroup.mk (s := N) φ) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  set f := QuotientGroup.mk' A with hf
  have hΦhat : frattini (G ⧸ A) = (frattini G).map f := frattini_quotient_eq G A hAΦ
  have hΦNhat : (frattini G).map f ≤ N.map f := Subgroup.map_mono hΦN
  have hΦNbar : frattini (N.map f) = ⊥ := by
    let fN : N →* N.map f := f.subgroupMap N
    have hfN : Function.Surjective fN := f.subgroupMap_surjective N
    have hker : fN.ker = frattini N := by
      have := Subgroup.ker_subgroupMap N f
      rw [this, hf, QuotientGroup.ker_mk', hA]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    let e : (N ⧸ fN.ker) ≃* N.map f := QuotientGroup.quotientKerEquivOfSurjective fN hfN
    have h1 : frattini (N ⧸ fN.ker) = ⊥ := by
      rw [frattini_quotient_eq N fN.ker (le_of_eq hker), Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact hker.symm.le
    rw [← frattini_map_equiv e, h1, Subgroup.map_bot]
  have hcardΦh : Nat.card (frattini (G ⧸ A)) ∣ Nat.card (frattini G) := by
    rw [hΦhat]; exact Subgroup.card_map_dvd _ _
  have hΦle : frattini G ≤ A := by
    by_contra hnle
    have hne : (frattini G).map f ≠ ⊥ := by
      intro h
      apply hnle
      rw [Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at h
      exact h
    have hne2 : frattini (G ⧸ A) ≠ ⊥ := hΦhat ▸ hne
    have hnil : Group.IsNilpotent (frattini (G ⧸ A)) := frattini_nilpotent
    have hnt : Nontrivial (frattini (G ⧸ A)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne2
    have hcenter : Subgroup.center (frattini (G ⧸ A)) ≠ ⊥ := Group.IsNilpotent.center_ne_bot _
    set V : Subgroup (G ⧸ A) := (Subgroup.center (frattini (G ⧸ A))).map (frattini (G ⧸ A)).subtype
      with hV
    have hVn : V.Normal := ConjAct.normal_of_characteristic_of_normal
    have hVc : IsMulCommutative V := ⟨⟨fun a b => by
      obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : G ⧸ A) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb') a')⟩⟩
    have hVΦ : V ≤ frattini (G ⧸ A) := Subgroup.map_subtype_le _
    have hVN : V ≤ N.map f := hVΦ.trans (hΦhat ▸ hΦNhat)
    have hVp : ¬ p ∣ Nat.card V := by
      intro hdvd
      apply hpΦ
      exact hdvd.trans ((Subgroup.card_dvd_of_le hVΦ).trans hcardΦh)
    have hidx : ∃ m : ℕ, (N.map f).index = p ^ m := by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hN
      refine ⟨m, ?_⟩
      have hkerN : f.ker ≤ N := by
        rw [hf, QuotientGroup.ker_mk']
        exact Subgroup.map_subtype_le _
      rw [Subgroup.index_map_eq N (QuotientGroup.mk'_surjective A) hkerN]
      exact hm
    have hVbot := eq_bot_of_frattini_of_index (N.map f) hΦNbar hidx V hVΦ hVN hVp
    apply hcenter
    exact (Subgroup.map_eq_bot_iff_of_injective _ (frattini (G ⧸ A)).subtype_injective).mp hVbot
  exact le_antisymm hAΦ hΦle


theorem action_kernel_is_frattini {H A : Type*} [Group H] [Group A] [Finite H] {p : ℕ}
    [Fact p.Prime] (ρ : H →* A) (hρ : Function.Surjective ρ) (L Q : Subgroup H) [L.Normal]
    [Q.Normal] (hL : IsPGroup p (H ⧸ L)) (hQD : Q ≤ ρ.ker)
    (hQsyl : ¬ p ∣ (Q.subgroupOf ρ.ker).index)
    (hfr : (ρ.ker.subgroupOf L).map (QuotientGroup.mk' (Q.subgroupOf L)) ≤
      frattini (L ⧸ Q.subgroupOf L))
    (hA : frattini A = ⊥) :
    ρ.ker.map (QuotientGroup.mk' Q) = frattini (H ⧸ Q) ∧
      ∃ e : ((H ⧸ Q) ⧸ frattini (H ⧸ Q)) ≃* A,
        ∀ h : H, e (QuotientGroup.mk (QuotientGroup.mk h)) = ρ h := by
  classical
  set D : Subgroup H := ρ.ker with hD
  let ρb : H ⧸ Q →* A := QuotientGroup.lift Q ρ hQD
  have hρb : Function.Surjective ρb := by
    intro a
    obtain ⟨h, rfl⟩ := hρ a
    exact ⟨QuotientGroup.mk h, rfl⟩
  have hkerb : ρb.ker = D.map (QuotientGroup.mk' Q) := QuotientGroup.ker_lift Q ρ hQD
  have hle1 : frattini (H ⧸ Q) ≤ D.map (QuotientGroup.mk' Q) := by
    have h1 := frattini_le_comap_frattini_of_surjective (φ := ρb) hρb
    rw [hA, MonoidHom.comap_bot, hkerb] at h1
    exact h1
  have hDLQ : ∀ x ∈ D, ∃ l ∈ D ⊓ L, ∃ q ∈ Q, x = l * q := by
    intro x hx
    set m := (Q.subgroupOf D).index with hm
    have hxm : x ^ m ∈ Q := by
      have := Subgroup.pow_index_mem (Q.subgroupOf D) (⟨x, hx⟩ : D)
      simpa [Subgroup.mem_subgroupOf] using this
    obtain ⟨k, hk⟩ := hL (QuotientGroup.mk x)
    have hxk : x ^ (p ^ k) ∈ L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hk
    have hcop : Nat.Coprime (p ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hQsyl)
    have hbez := Nat.gcd_eq_gcd_ab (p ^ k) m
    rw [hcop] at hbez
    set a : ℤ := Nat.gcdA (p ^ k) m
    set b : ℤ := Nat.gcdB (p ^ k) m
    have hx1 : x = (x ^ (p ^ k)) ^ a * (x ^ m) ^ b := by
      have : x = x ^ (((p ^ k : ℕ) : ℤ) * a + (m : ℤ) * b) := by
        have h' : ((p ^ k : ℕ) : ℤ) * a + (m : ℤ) * b = 1 := by
          rw [← hbez]; simp
        rw [h', zpow_one]
      conv_lhs => rw [this]
      rw [zpow_add, zpow_mul, zpow_mul]
      simp only [zpow_natCast]
    have hl : (x ^ (p ^ k)) ^ a ∈ L := zpow_mem hxk a
    have hq : (x ^ m) ^ b ∈ Q := zpow_mem hxm b
    refine ⟨(x ^ (p ^ k)) ^ a, ⟨?_, hl⟩, (x ^ m) ^ b, hq, hx1⟩
    have : (x ^ (p ^ k)) ^ a = x * ((x ^ m) ^ b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hx1.symm
    rw [this]
    exact D.mul_mem hx (D.inv_mem (hQD hq))
  have hLbar_normal : (L.map (QuotientGroup.mk' Q)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Q)
  have hDL : ∀ l ∈ D ⊓ L, QuotientGroup.mk' Q l ∈ frattini (H ⧸ Q) := by
    intro l hl
    let jL : L →* L.map (QuotientGroup.mk' Q) := (QuotientGroup.mk' Q).subgroupMap L
    have hjL : Function.Surjective jL := (QuotientGroup.mk' Q).subgroupMap_surjective L
    have hjker : Q.subgroupOf L ≤ jL.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have : (y : H) ∈ Q := hy
      show QuotientGroup.mk' Q (y : H) = 1
      exact (QuotientGroup.eq_one_iff _).mpr this
    have hmem : jL ⟨l, hl.2⟩ ∈ frattini (L.map (QuotientGroup.mk' Q)) := by
      unfold frattini Order.radical
      refine Subgroup.mem_iInf.mpr fun Mb => Subgroup.mem_iInf.mpr fun hMb => ?_
      have hMt : IsCoatom (Mb.comap jL) := isCoatom_comap_of_surjective hjL hMb
      have hQM : Q.subgroupOf L ≤ Mb.comap jL := fun y hy => by
        have : jL y = 1 := hjker hy
        show jL y ∈ Mb
        rw [this]; exact one_mem _
      have hkerM : (QuotientGroup.mk' (Q.subgroupOf L)).ker ≤ Mb.comap jL := by
        rw [QuotientGroup.ker_mk']; exact hQM
      have hMc := isCoatom_map_of_ker_le (QuotientGroup.mk' (Q.subgroupOf L))
        (QuotientGroup.mk'_surjective _) hMt hkerM
      have h2 := frattini_le_coatom hMc (hfr ⟨⟨l, hl.2⟩, hl.1, rfl⟩)
      obtain ⟨y, hy, hyl⟩ := h2
      have hyl' : (y⁻¹ * ⟨l, hl.2⟩ : L) ∈ Q.subgroupOf L := QuotientGroup.eq.mp hyl
      have := mul_mem hy (hQM hyl')
      rw [mul_inv_cancel_left] at this
      exact this
    have h3 : (frattini (L.map (QuotientGroup.mk' Q))).map
        (L.map (QuotientGroup.mk' Q)).subtype ≤ frattini (H ⧸ Q) :=
      frattini_le_frattini_of_normal (H ⧸ Q) (L.map (QuotientGroup.mk' Q))
    exact h3 ⟨jL ⟨l, hl.2⟩, hmem, rfl⟩
  have hle2 : D.map (QuotientGroup.mk' Q) ≤ frattini (H ⧸ Q) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨l, hl, q, hq, rfl⟩ := hDLQ x hx
    have hqq : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    have : QuotientGroup.mk' Q (l * q) = QuotientGroup.mk' Q l := by
      rw [map_mul, hqq, mul_one]
    rw [this]
    exact hDL l hl
  have hEq : D.map (QuotientGroup.mk' Q) = frattini (H ⧸ Q) := le_antisymm hle2 hle1
  refine ⟨hEq, ?_⟩
  have hfr_eq : frattini (H ⧸ Q) = ρb.ker := by rw [hkerb, hEq]
  let e : ((H ⧸ Q) ⧸ frattini (H ⧸ Q)) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hfr_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρb hρb)
  refine ⟨e, fun h => ?_⟩
  simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end CFSG.QuasithinUnique.Setup.Campbell
