module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion
public import CFSG.ClassicalInvolution.TwoGroupCase.Packets
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

section Sylow

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

theorem commute_of_conj_sylow (hz : orderOf z = 2)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set F))
    (hKn : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F))
    (Qs : Sylow 2 ↥K)
    (hQ : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Qs : Subgroup ↥K) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hzQ : z ∈ (Qs : Subgroup ↥K).map K.subtype) {T : Subgroup F} (hT : IsPGroup 2 T)
    (hQT : (Qs : Subgroup ↥K).map K.subtype ≤ T) {g : F}
    (hg : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom ≠
      (Qs : Subgroup ↥K).map K.subtype) :
    ∀ x ∈ ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom,
      ∀ y ∈ (Qs : Subgroup ↥K).map K.subtype, x * y = y * x := by
  have hRn : (K.subgroupOf (Subgroup.centralizer ({z} : Set F))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hKn
  have h1 : conjSubgroup g ((Qs : Subgroup ↥K).map K.subtype) =
      ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom := rfl
  have h2 : conjSubgroup (1 : F) ((Qs : Subgroup ↥K).map K.subtype) =
      (Qs : Subgroup ↥K).map K.subtype := by
    ext x
    simp [conjSubgroup]
  have := quaternion_conjugates_commute Qs hQ hzQ hz hKC hRn hT hQT (h := g) (k := 1)
    (by rw [h1]; exact hg) (by rw [h2]; exact hQT) (by rw [h1, h2]; exact hne)
  rw [h1, h2] at this
  exact this.2

theorem IsClassical2A7.mem_sylow {Y L : Subgroup F} {u : F} (h : IsClassical2A7 Y L u)
    (Qs : Sylow 2 ↥L) : u ∈ (Qs : Subgroup ↥L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvdK : 2 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L h.mem
    rwa [h.orderOf_eq_two] at this
  have hdvd : 2 ∣ Nat.card (Qs : Subgroup ↥L) := by
    rw [Sylow.card_eq_multiplicity Qs]
    have : 1 ≤ (Nat.card L).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvdK
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (Qs : Subgroup ↥L)) 2 hdvd
  have hx' : orderOf (((x : ↥(Qs : Subgroup ↥L)) : ↥L) : F) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hx
  have hxu := h.eq_of_orderOf_eq_two ((x : ↥(Qs : Subgroup ↥L)) : ↥L).2 hx'
  exact ⟨(x : ↥L), x.2, hxu⟩

theorem TightSetting.conj_mem_Zset_of_sylow (S : TightSetting F K z) {T : Subgroup F}
    (hT : IsPGroup 2 T) (Qs : Sylow 2 ↥K)
    (hQT : (Qs : Subgroup ↥K).map K.subtype ≤ T) {g : F}
    (hg : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ T) :
    g * z * g⁻¹ ∈ Zset K z := by
  have hKz := S.tight.classical
  have hzQ : z ∈ (Qs : Subgroup ↥K).map K.subtype := hKz.mem_sylow Qs
  have hgz : g * z * g⁻¹ ∈ classOf z := ⟨g, rfl⟩
  have hgzQ : g * z * g⁻¹ ∈ ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom :=
    ⟨z, hzQ, rfl⟩
  by_cases hne : ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom =
      (Qs : Subgroup ↥K).map K.subtype
  ·
    rw [hne] at hgzQ
    have hgzK : g * z * g⁻¹ ∈ K := by
      obtain ⟨y, _, hy⟩ := hgzQ
      rw [← hy]; exact y.2
    have : g * z * g⁻¹ = z := hKz.eq_of_orderOf_eq_two hgzK
      (orderOf_eq_two_of_mem_classOf S.tight hgz)
    rw [this]
    exact S.self_mem_Zset
  · have hcomm := commute_of_conj_sylow hKz.orderOf_eq_two hKz.le_centralizer S.tight.tight Qs
      (exists_quaternion_sylow_of_witness hKz.witness Qs) hzQ hT hQT hg hne
    have hcentK : ∀ q' ∈ ((Qs : Subgroup ↥K).map K.subtype).map (MulAut.conj g).toMonoidHom,
        ∀ k ∈ K, k * q' = q' * k := by
      intro q' hq' k hk
      have hq'z : z * q' = q' * z := (hcomm q' hq' z hzQ).symm
      have hq'N : q' ∈ Subgroup.normalizer (K : Set F) := S.tight.tight (by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hq'z)
      have htriv := oddQuotAut_conjOn_eq_one hKz.witness Qs hq'N (fun q hq => by
        have := hcomm q' hq' (q : F) ⟨q, hq, rfl⟩
        exact this)
      exact centralizes_of_oddQuotAut_eq_one hKz.perfect (S.P1 K z hKz) hq'N htriv k hk
    have hKw : memb K z z ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set F) := by
      rw [memb_self S.tight]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact (hcentK _ hgzQ k hk).symm
    have hLw : memb K z (g * z * g⁻¹) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set F) :=
      (S.tight.memb hgz).classical.le_centralizer
    have h := S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight hgz) (mem_classOf_self z) hgz hKw hLw
    rw [memb_self S.tight] at h
    exact ⟨hgz, h⟩

end Sylow

section Strong

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem CommOrEq.map_conj {L M : Subgroup F} (h : CommOrEq L M) (g : F) :
    CommOrEq (L.map (MulAut.conj g).toMonoidHom) (M.map (MulAut.conj g).toMonoidHom) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · refine Or.inr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    have := h a ha b hb
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [this]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

omit [Finite F] in
theorem TightSetting.Zset_rebase_eq (S : TightSetting F K z) {x : F} (hx : x ∈ classOf z) :
    Zset (memb K z x) x =
      {u | u ∈ classOf z ∧ CommOrEq (memb K z x) (memb K z u)} := by
  ext u
  have hclass : classOf x = classOf z := classOf_eq_of_mem hx
  constructor
  · rintro ⟨hu, hc⟩
    have hu' : u ∈ classOf z := by rwa [hclass] at hu
    rw [memb_memb S.tight hx hu'] at hc
    exact ⟨hu', hc⟩
  · rintro ⟨hu, hc⟩
    refine ⟨by rw [hclass]; exact hu, ?_⟩
    rw [memb_memb S.tight hx hu]
    exact hc

omit [Finite F] in
theorem TightSetting.Zset_rebase (S : TightSetting F K z) {w : F} (hw : w ∈ Zset K z) :
    Zset (memb K z w) w = Zset K z := by
  rw [S.Zset_rebase_eq hw.1]
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have h1 : CommOrEq (memb K z z) (memb K z w) := by rw [memb_self S.tight]; exact hw.2
    have := S.commOrEq_trans (mem_classOf_self z) hw.1 hu h1 hc
    rwa [memb_self S.tight] at this
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have h1 : CommOrEq (memb K z w) (memb K z z) := by rw [memb_self S.tight]; exact hw.2.symm
    have h2 : CommOrEq (memb K z z) (memb K z u) := by rw [memb_self S.tight]; exact hc
    exact S.commOrEq_trans hw.1 (mem_classOf_self z) hu h1 h2

omit [Finite F] in
theorem TightSetting.mem_Zset_of_mem_rebase (S : TightSetting F K z) {x a : F}
    (hx : x ∈ classOf z) (ha : a ∈ Zset K z) (ha' : a ∈ Zset (memb K z x) x) :
    x ∈ Zset K z := by
  rw [S.Zset_rebase_eq hx] at ha'
  refine ⟨hx, ?_⟩
  have h1 : CommOrEq (memb K z z) (memb K z a) := by rw [memb_self S.tight]; exact ha.2
  exact by
    have := S.commOrEq_trans (mem_classOf_self z) ha.1 hx h1 ha'.2.symm
    rwa [memb_self S.tight] at this

theorem TightSetting.mem_normalizer_of_sylow (S : TightSetting F K z) {R : Subgroup F}
    (hR : ABGLocalTools.IsSylowOf 2 R (cliqueSub K z)) {T : Subgroup F} (hT : IsPGroup 2 T)
    (hRT : R ≤ T) : ∀ s ∈ T, s ∈ Subgroup.normalizer (Zset K z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ s ∈ T, ∀ n ∈ Zset K z, s * n * s⁻¹ ∈ Zset K z := by
    intro s hs n hn
    have hSyl := hR.inf_of_le_normalizer (memb_le_cliqueSub hn) (S.cliqueSub_le_normalizer hn)
    obtain ⟨Qs, hQs⟩ := hSyl
    have hQT : (Qs : Subgroup ↥(memb K z n)).map (memb K z n).subtype ≤ T := by
      rw [hQs]; exact inf_le_left.trans hRT
    have hconj : ((Qs : Subgroup ↥(memb K z n)).map (memb K z n).subtype).map
        (MulAut.conj s).toMonoidHom ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      exact T.mul_mem (T.mul_mem hs (hQT hy)) (T.inv_mem hs)
    have := (S.rebase hn.1).conj_mem_Zset_of_sylow hT Qs hQT hconj
    rwa [S.Zset_rebase hn] at this
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨key s hs n, fun hsn => ?_⟩
  have := key s⁻¹ (T.inv_mem hs) _ hsn
  simpa [mul_assoc] using this

omit [Finite F] in
theorem TightSetting.E_le_normalizer (S : TightSetting F K z) :
    Subgroup.closure (Zset K z) ≤ Subgroup.normalizer (Zset K z) := by
  intro x hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · intro hn
    have : x * n * x⁻¹ = n := by rw [S.E_centralizes hx hn]; group
    rw [this]; exact hn
  · intro hw
    have h1 := S.E_centralizes (Subgroup.inv_mem _ hx) hw
    have : n = x * n * x⁻¹ := by
      calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
        _ = ((x * n * x⁻¹) * x⁻¹) * x := by rw [h1]
        _ = x * n * x⁻¹ := by group
    rw [this]; exact hw

theorem TightSetting.strongly_closed (S : TightSetting F K z) {T : Subgroup F}
    (hT : ∀ s ∈ T, s ∈ Subgroup.normalizer (Zset K z)) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) {g : F} (hgT : g * e * g⁻¹ ∈ T) :
    g * e * g⁻¹ ∈ Subgroup.closure (Zset K z) := by
  by_cases he1 : e = 1
  · rw [he1]
    simp
  obtain ⟨e', he'⟩ : ∃ e' : F, e' = g * e * g⁻¹ := ⟨_, rfl⟩
  rw [← he'] at hgT ⊢
  have he'1 : e' ≠ 1 := by
    intro h
    apply he1
    have : g * e * g⁻¹ = 1 := by rw [← he']; exact h
    simpa using this
  obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : F, x₀ = g * z * g⁻¹ := ⟨_, rfl⟩
  have hx₀ : x₀ ∈ classOf z := ⟨g, hx₀def.symm⟩
  have S₀ := S.rebase hx₀
  have hZ'sub : ∀ w ∈ Zset K z, g * w * g⁻¹ ∈ Zset (memb K z x₀) x₀ := by
    intro w hw
    rw [S.Zset_rebase_eq hx₀]
    refine ⟨mem_classOf_conj hw.1 g, ?_⟩
    have h1 : memb K z x₀ = K.map (MulAut.conj g).toMonoidHom := by
      rw [hx₀def, memb_conj S.tight (mem_classOf_self z) g, memb_self S.tight]
    have h2 : memb K z (g * w * g⁻¹) = (memb K z w).map (MulAut.conj g).toMonoidHom :=
      memb_conj S.tight hw.1 g
    rw [h1, h2]
    exact CommOrEq.map_conj hw.2 g
  have hc1 : e' ∈ Subgroup.closure (Zset (memb K z x₀) x₀) := by
    have hmapsub : (Subgroup.closure (Zset K z)).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.closure (Zset (memb K z x₀) x₀) := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨w, hw, rfl⟩
      exact hZ'sub w hw
    rw [he']
    exact hmapsub ⟨e, he, rfl⟩
  have hsq : e' * e' = 1 := by
    have := S.E_sq he
    rw [he']
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hN : e' ∈ Subgroup.normalizer (Zset K z) := hT e' hgT
  by_cases hA : ∃ a ∈ Zset K z, e' * a = a * e'
  · obtain ⟨a, haZ, hcomm⟩ := hA
    have haC : a ∈ Subgroup.centralizer ({e'} : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hcomm
    have haN : a ∈ Subgroup.normalizer (Zset (memb K z x₀) x₀) :=
      S₀.centralizer_le_setNormalizer hc1 he'1 haC
    have haclass : a ∈ classOf x₀ := by rw [classOf_eq_of_mem hx₀]; exact haZ.1
    have haZ' := S₀.mem_Zset_of_mem_normalizer haclass haN
    have hx₀Z := S.mem_Zset_of_mem_rebase hx₀ haZ haZ'
    rw [S.Zset_rebase hx₀Z] at hc1
    exact hc1
  · push Not at hA
    have hfix : ∀ x ∈ Zset K z, e' * x * e'⁻¹ ≠ x := by
      intro x hx h
      apply hA x hx
      have : e' * x = x * e' := by
        calc e' * x = (e' * x * e'⁻¹) * e' := by group
          _ = x * e' := by rw [h]
      exact this
    have hLu : memb K z x₀ ≤ Subgroup.centralizer ({e'} : Set F) := by
      have h1 := S₀.closure_Zset_le_centralizer S₀.self_mem_Zset hc1
      rw [memb_self S₀.tight] at h1
      exact le_centralizer_singleton_of_mem_centralizer h1
    obtain ⟨hbZ, hbz, hzb, he0_clos, he01⟩ := S.swap_data hN hfix
    rcases S.swap_lemma hsq he'1 hN hfix (S.tight.memb hx₀).classical hLu with h | h
    ·
      have hx₀E : x₀ ∈ Subgroup.closure (Zset K z) := by rw [h]; exact he0_clos
      have hx₀Z : x₀ ∈ Zset K z :=
        S.mem_Zset_of_mem_normalizer hx₀ (S.E_le_normalizer hx₀E)
      have hcomm := S₀.E_centralizes hc1 (S₀.self_mem_Zset)
      exfalso
      apply hfix x₀ hx₀Z
      calc e' * x₀ * e'⁻¹ = x₀ * e' * e'⁻¹ := by rw [hcomm]
        _ = x₀ := by group
    · have hx₀Z : x₀ ∈ Zset K z := (S.memb_le_centralizer_iff he0_clos he01 hx₀).mp h
      rw [S.Zset_rebase hx₀Z] at hc1
      exact hc1

@[expose] def GoldschmidtStronglyClosedExponent : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (T : Sylow 2 F) (A : Subgroup F), A ≠ ⊥ → A ≤ (T : Subgroup F) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, ∀ g : F, g * a * g⁻¹ ∈ (T : Subgroup F) → g * a * g⁻¹ ∈ A) →
      ∀ x ∈ (T : Subgroup F), x ^ 4 = 1

theorem TightSetting.false_of_goldschmidt [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (S : TightSetting F K z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := ABGLocalTools.exists_isSylowOf 2 (cliqueSub K z)
  obtain ⟨T, hRT⟩ := hR.isPGroup.exists_le_sylow
  have hTs : ∀ s ∈ (T : Subgroup F), s ∈ Subgroup.normalizer (Zset K z) :=
    S.mem_normalizer_of_sylow hR T.isPGroup' hRT
  have hZR : ∀ w ∈ Zset K z, w ∈ R := by
    intro w hw
    have hSyl := hR.inf_of_le_normalizer (memb_le_cliqueSub hw) (S.cliqueSub_le_normalizer hw)
    obtain ⟨Qs, hQs⟩ := hSyl
    have := (S.tight.memb hw.1).classical.mem_sylow Qs
    rw [hQs] at this
    exact this.1
  have hER : Subgroup.closure (Zset K z) ≤ R := (Subgroup.closure_le R).mpr hZR
  have hzne : z ≠ 1 := S.ne_one (mem_classOf_self z)
  have hexp := GS F hnab T (Subgroup.closure (Zset K z)) (by
      intro h
      apply hzne
      have : z ∈ Subgroup.closure (Zset K z) := Subgroup.subset_closure S.self_mem_Zset
      rw [h] at this
      simpa using this)
    (hER.trans hRT) (fun a ha b hb => S.E_comm ha hb)
    (fun a ha g hg => S.strongly_closed hTs ha hg)
  have hSylK : ABGLocalTools.IsSylowOf 2 (R ⊓ memb K z z) (memb K z z) :=
    hR.inf_of_le_normalizer (memb_le_cliqueSub S.self_mem_Zset)
      (S.cliqueSub_le_normalizer S.self_mem_Zset)
  rw [memb_self S.tight] at hSylK
  obtain ⟨Qs, hQs⟩ := hSylK
  obtain ⟨x, hx, hx8⟩ := exists_orderOf_eight_of_witness S.tight.classical.witness Qs
  have hxR : (x : F) ∈ R ⊓ K := by
    rw [← hQs]
    exact ⟨x, hx, rfl⟩
  have h4 := hexp (x : F) (hRT hxR.1)
  have : orderOf (x : F) = 8 := by rw [← Subgroup.orderOf_coe] at hx8; exact hx8
  have hdvd : orderOf (x : F) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [this] at hdvd
  omega

end Strong

end CFSG.ClassicalInvolution.Hat2A7
