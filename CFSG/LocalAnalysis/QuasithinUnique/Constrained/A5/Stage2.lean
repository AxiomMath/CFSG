module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Q8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Z
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped commutatorElement

@[expose] def Evens : Finset (Fin 5 → ZMod 2) := Finset.univ.filter isEven

theorem mem_Evens {v : Fin 5 → ZMod 2} : v ∈ Evens ↔ isEven v := by simp [Evens]

@[expose] def zraw : RP := (z0, 1)

@[expose] def commZ (r r' : RP) : Prop :=
  rmul r r' = rmul r' r ∨ rmul r r' = rmul (rmul r' r) zraw

instance : DecidableRel commZ := fun r r' => by unfold commZ; infer_instance

@[expose] def inPraw (r : RP) : Prop := isE8 r.1 ∧ r.2 ∈ Vset

@[expose] def w04w : evenWeight 5 := ⟨w04, w04_even⟩

theorem s3_mem : s3 ∈ Dset := by decide +kernel

theorem sa_sc_comm : sa * sc * sa⁻¹ * sc⁻¹ = s1 := by decide +kernel

theorem P_commZ : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, ∀ v' ∈ Evens, v' 4 = 0 → ∀ σ' ∈ Vset,
    commZ (v, σ) (v', σ') := by decide +kernel

theorem csW : ∀ v ∈ Evens, ∀ σ ∈ Dset, commZ (v, σ) (w04 + pact sa w04, 1) →
    commZ (v, σ) (w04 + pact sc w04, 1) → commZ (v, σ) (w04 + pact s3 w04, 1) →
    commZ (v, σ) (0, s1) → v 4 = 0 ∧ σ ∈ Vset := by decide +kernel

theorem conj_mem_commutator {G : Type*} [Group G] {S : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (S : Set G)) {c : G} (hc : c ∈ ⁅S, S⁆) :
    y * c * y⁻¹ ∈ ⁅S, S⁆ := by
  have h : ⁅S, S⁆ ≤ (⁅S, S⁆).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    show y * ⁅g₁, g₂⁆ * y⁻¹ ∈ ⁅S, S⁆
    have e : y * ⁅g₁, g₂⁆ * y⁻¹ = ⁅y * g₁ * y⁻¹, y * g₂ * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hy g₁).mp hg₁)
      ((Subgroup.mem_normalizer_iff.mp hy g₂).mp hg₂)
  exact h hc

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] noncomputable def raw (h : ↥H) : RP := ((X.cw h).1, C.D.π h)

theorem raw_mul (h h' : ↥H) : X.raw (h * h') = rmul (X.raw h) (X.raw h') := by
  unfold raw rmul
  rw [X.cw_mul, map_mul]
  rfl

theorem raw_inj {h h' : ↥H} (e : X.raw h = X.raw h') : h = h' := by
  have hv : X.cw h = X.cw h' := Subtype.ext (congrArg Prod.fst e)
  have hπ : C.D.π h = C.D.π h' := congrArg Prod.snd e
  calc h = X.emb (X.cw h) (C.D.π h) := X.cw_spec h
    _ = X.emb (X.cw h') (C.D.π h') := by rw [hv, hπ]
    _ = h' := (X.cw_spec h').symm

theorem iV_eq_emb (w : evenWeight 5) : C.iV w = X.emb w 1 := by
  rw [Sec.emb, map_one, mul_one]

theorem raw_iV (w : evenWeight 5) : X.raw (C.iV w) = (w.1, 1) := by
  unfold raw
  rw [X.iV_eq_emb, X.cw_emb, X.pi_emb]

theorem raw_emb (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)) :
    X.raw (X.emb w σ) = (w.1, σ) := by
  unfold raw
  rw [X.cw_emb, X.pi_emb]

theorem raw_s (σ : Equiv.Perm (Fin 5)) : X.raw (X.s σ) = (0, σ) := by
  have h : X.s σ = X.emb 0 σ := by rw [Sec.emb, C.iV_zero, one_mul]
  rw [h, X.raw_emb]
  rfl

theorem raw_P_iff (h : ↥H) : (h : G) ∈ borelP M L ↔ inPraw (X.raw h) := by
  constructor
  · intro hh
    rw [X.borelP_eq] at hh
    obtain ⟨w, σ, hσ, hw, hx⟩ := hh
    have : h = X.emb w σ := Subtype.ext hx
    rw [this, X.raw_emb]
    exact ⟨⟨w.2, hw⟩, hσ⟩
  · intro h1
    rw [X.borelP_eq]
    exact ⟨X.cw h, C.D.π h, (mem_Vstd _).mpr h1.2, h1.1.2, congrArg Subtype.val (X.cw_spec h)⟩

theorem commZ_iff (a b : ↥H) :
    commZ (X.raw a) (X.raw b) ↔ (a : G) * b = b * a ∨ (a : G) * b = b * a * C.zU := by
  have hz : zraw = X.raw (C.iV StdCfg.z0V) := (X.raw_iV StdCfg.z0V).symm
  unfold commZ
  rw [hz, ← X.raw_mul, ← X.raw_mul, ← X.raw_mul]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val (X.raw_inj h))
    · exact Or.inr (congrArg Subtype.val (X.raw_inj h))
  · rintro (h | h)
    · exact Or.inl (congrArg X.raw (Subtype.ext h))
    · exact Or.inr (congrArg X.raw (Subtype.ext h))

theorem P_comm {q q' : G} (hq : q ∈ borelP M L) (hq' : q' ∈ borelP M L) :
    q * q' = q' * q ∨ q * q' = q' * q * C.zU := by
  have hqH : q ∈ H := C.hcs.sylow.le (X.P_le_S hq)
  have hqH' : q' ∈ H := C.hcs.sylow.le (X.P_le_S hq')
  have hr := (X.raw_P_iff ⟨q, hqH⟩).mp hq
  have hr' := (X.raw_P_iff ⟨q', hqH'⟩).mp hq'
  exact (X.commZ_iff ⟨q, hqH⟩ ⟨q', hqH'⟩).mp
    (P_commZ _ (mem_Evens.mpr hr.1.1) hr.1.2 _ hr.2 _ (mem_Evens.mpr hr'.1.1) hr'.1.2 _ hr'.2)

theorem comm_S_le_P : ⁅S, S⁆ ≤ borelP M L := by
  have : Fact (IsPGroup 2 ↥S) := ⟨C.hcs.sylow.2.1⟩
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hc : ⁅(⟨g₁, hg₁⟩ : ↥S), (⟨g₂, hg₂⟩ : ↥S)⁆ ∈ frattini ↥S := by
    apply CFSG.commutator_le_frattini_of_isPGroup (R := ↥S) (p := 2)
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact X.frattini_le ⟨_, hc, rfl⟩

theorem iV_mem_comm {a : Equiv.Perm (Fin 5)} (ha : a ∈ Dset) (w : evenWeight 5) :
    ((C.iV (w + vact a w) : ↥H) : G) ∈ ⁅S, S⁆ := by
  have h := congrArg Subtype.val (X.iV_comm_key a w)
  have hc := Subgroup.commutator_mem_commutator (C.iV_mem_S w) (X.s_mem_S ha)
  rw [← h]
  exact hc

theorem s1_mem_comm : ((X.s s1 : ↥H) : G) ∈ ⁅S, S⁆ := by
  have h : ⁅X.s sa, X.s sc⁆ = X.s s1 := by
    rw [← map_commutatorElement (X.s) sa sc, commutatorElement_def, sa_sc_comm]
  have hc := Subgroup.commutator_mem_commutator (X.s_mem_S sa_mem) (X.s_mem_S sc_mem)
  rw [← congrArg Subtype.val h]
  exact hc

theorem conj_P_mem {y : G} (hy : y ∈ Subgroup.normalizer (S : Set G))
    (hyz : y * C.zU * y⁻¹ = C.zU) {p : G} (hp : p ∈ borelP M L) :
    y * p * y⁻¹ ∈ borelP M L := by
  have hyi : y⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hy
  have hqS : y * p * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hy p).mp (X.P_le_S hp)
  have hqH : y * p * y⁻¹ ∈ H := C.hcs.sylow.le hqS
  have hcomm : ∀ f ∈ ⁅S, S⁆, (y * p * y⁻¹) * f = f * (y * p * y⁻¹) ∨
      (y * p * y⁻¹) * f = f * (y * p * y⁻¹) * C.zU := by
    intro f hf
    have hf' : y⁻¹ * f * y⁻¹⁻¹ ∈ ⁅S, S⁆ := conj_mem_commutator hyi hf
    rcases X.P_comm hp (X.comm_S_le_P hf') with h | h
    · left
      calc y * p * y⁻¹ * f = y * (p * (y⁻¹ * f * y⁻¹⁻¹)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * f * y⁻¹⁻¹) * p) * y⁻¹ := by rw [h]
        _ = f * (y * p * y⁻¹) := by group
    · right
      calc y * p * y⁻¹ * f = y * (p * (y⁻¹ * f * y⁻¹⁻¹)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * f * y⁻¹⁻¹) * p * C.zU) * y⁻¹ := by rw [h]
        _ = f * (y * p * y⁻¹) * (y * C.zU * y⁻¹) := by group
        _ = f * (y * p * y⁻¹) * C.zU := by rw [hyz]
  let q : ↥H := ⟨y * p * y⁻¹, hqH⟩
  have c1 : commZ (X.raw q) (X.raw (C.iV (w04w + vact sa w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_comm sa_mem w04w))
  have c2 : commZ (X.raw q) (X.raw (C.iV (w04w + vact sc w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_comm sc_mem w04w))
  have c3 : commZ (X.raw q) (X.raw (C.iV (w04w + vact s3 w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_comm s3_mem w04w))
  have c4 : commZ (X.raw q) (X.raw (X.s s1)) :=
    (X.commZ_iff _ _).mpr (hcomm _ X.s1_mem_comm)
  rw [X.raw_iV] at c1 c2 c3
  rw [X.raw_s] at c4
  have hq := csW (X.raw q).1 (mem_Evens.mpr (X.cw q).2) (X.raw q).2
    ((mem_Dstd _).mp ((X.mem_S_iff q).mp hqS)) c1 c2 c3 c4
  exact (X.raw_P_iff q).mpr ⟨⟨(X.cw q).2, hq.1⟩, hq.2⟩

theorem normalizes_P {y : G} (hy : y ∈ Subgroup.normalizer (S : Set G))
    (hyz : y * C.zU * y⁻¹ = C.zU) : y ∈ Subgroup.normalizer (borelP M L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => X.conj_P_mem hy hyz hg, fun hg => ?_⟩
  have hy' : y⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hy
  have hyz' : y⁻¹ * C.zU * y⁻¹⁻¹ = C.zU := by
    have h : y⁻¹ * (y * C.zU * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * C.zU * y⁻¹⁻¹ := by rw [hyz]
    calc y⁻¹ * C.zU * y⁻¹⁻¹ = y⁻¹ * (y * C.zU * y⁻¹) * y⁻¹⁻¹ := h.symm
      _ = C.zU := by group
  have := X.conj_P_mem hy' hyz' hg
  have e : y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g := by group
  rwa [e] at this

theorem T_cent_z {t : G} (ht : t ∈ T) : t * C.zU = C.zU * t := by
  have hz : C.zU ∈ centerOf T := X.Z_le ((X.centerOf_P_iff _).mpr (Or.inr rfl))
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 t ht

theorem K_cent_z {k : G} (hk : k ∈ borelK M L) : k * C.zU = C.zU * k := by
  rw [X.borelK_eq] at hk
  obtain ⟨w, σ, hσ, hw, rfl⟩ := hk
  exact C.zU_comm (X.emb w σ) (by rw [X.pi_emb]; exact ((mem_A4set σ).mp hσ).1)

theorem M1_cent : T ⊔ borelK M L ≤ Subgroup.centralizer (centerOf (borelP M L) : Set G) := by
  have key : ∀ x : G, x * C.zU = C.zU * x →
      x ∈ Subgroup.centralizer (centerOf (borelP M L) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases (X.centerOf_P_iff h).mp hh with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hx.symm
  exact sup_le (fun t ht => key t (X.T_cent_z ht)) (fun k hk => key k (X.K_cent_z hk))

theorem T_normalizes_P : T ≤ Subgroup.normalizer (borelP M L : Set G) := fun t ht =>
  X.normalizes_P (C.T_le_normalizer_S ht) (by
    calc t * C.zU * t⁻¹ = (C.zU * t) * t⁻¹ := by rw [X.T_cent_z ht]
      _ = C.zU := by group)

theorem K_normalizes_P : borelK M L ≤ Subgroup.normalizer (borelP M L : Set G) := by
  rw [X.borelK_eq, X.borelP_eq]
  exact X.Ksub_normalizes_Psub

theorem step2 (h1 : A5Step1 T M H S L) : A5Step2 T M H S L := by
  have hTC := X.hTC
  refine
    { toA5Step1 := h1
      M1_cent := X.M1_cent
      PTC_norm := ?_
      ZTC_eq := ?_
      TC_card := ?_
      TC_comm := ?_
      O2_cent := ?_
      H_cent := ?_ }
  · rw [hTC, sup_bot_eq]
    exact sup_le X.T_normalizes_P X.K_normalizes_P
  · rw [hTC, sup_bot_eq, sup_bot_eq]
  · rw [hTC, Subgroup.card_bot]
    norm_num
  · intro x _ _ h
    rw [hTC, Subgroup.card_bot] at h
    exact absurd h (by norm_num)
  · rw [hTC, sup_bot_eq]
    exact fun x hx => X.M1_cent (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hx)
  · rw [hTC]
    intro h _
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have : g = 1 := by simpa using hg
    rw [this, one_mul, mul_one]

end Sec

theorem a5_exists_sec
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) : ∃ C : StdCfg T M H S L, Nonempty (Sec C) := by
  have hcs := cfg.cs
  have hj := cfg.single
  have hTC := a5_TC_eq_bot h247 h245_4 hC54 h314 cfg
  have F := h247_facts h247 hcs cfg.alt5 hj
  have hQ := blockQ_eq_blockU h245_4 hcs hj
  obtain ⟨D, hsurj, hker, hRE, hRE', hHeq⟩ := exists_stdData hcs hj cfg.alt5 F hQ hC54
  exact ⟨⟨hcs, hj, F, D, hsurj, hker, hRE, hRE', hHeq⟩, exists_sec _ hTC⟩

theorem lemma2_4_29_2
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_2 := by
  intro G _ _ T M H S L cfg h1
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  exact X.step2 h1

end CFSG.QuasithinUnique.A5
