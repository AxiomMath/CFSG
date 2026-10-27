module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Seven

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace S56

theorem comm_conj_t {G : Type*} [Group G] {t ε a b j q : G}
    (hab : a * b = b * a) (hεε : ε * ε = 1) (haa : a * a = 1) (hbb : b * b = 1)
    (hjt : j * t * j⁻¹ = t) (hjε : j * ε * j⁻¹ = ε * b) (hja : j * a * j⁻¹ = a)
    (hjb : j * b * j⁻¹ = b)
    (hqt : q * t * q⁻¹ = t * ε) (hqε : q * ε * q⁻¹ = ε * a) (hqa : q * a * q⁻¹ = a)
    (hqb : q * b * q⁻¹ = b) :
    (j * q * j⁻¹ * q⁻¹) * t * (j * q * j⁻¹ * q⁻¹)⁻¹ = t * b := by
  have e1 : q⁻¹ * t * q = t * ε * a := by
    have h : q * (t * ε * a) * q⁻¹ = t := by
      calc q * (t * ε * a) * q⁻¹ = (q * t * q⁻¹) * (q * ε * q⁻¹) * (q * a * q⁻¹) := by group
        _ = t * (ε * ε) * (a * a) := by rw [hqt, hqε, hqa]; group
        _ = t := by rw [hεε, haa]; group
    calc q⁻¹ * t * q = q⁻¹ * (q * (t * ε * a) * q⁻¹) * q := by rw [h]
      _ = t * ε * a := by group
  have e2 : j⁻¹ * (t * ε * a) * j = t * (ε * b) * a := by
    have ht : j⁻¹ * t * j = t := by
      calc j⁻¹ * t * j = j⁻¹ * (j * t * j⁻¹) * j := by rw [hjt]
        _ = t := by group
    have hε : j⁻¹ * ε * j = ε * b := by
      have h : j * (ε * b) * j⁻¹ = ε := by
        calc j * (ε * b) * j⁻¹ = (j * ε * j⁻¹) * (j * b * j⁻¹) := by group
          _ = (ε * b) * b := by rw [hjε, hjb]
          _ = ε := by rw [mul_assoc, hbb, mul_one]
      calc j⁻¹ * ε * j = j⁻¹ * (j * (ε * b) * j⁻¹) * j := by rw [h]
        _ = ε * b := by group
    have ha : j⁻¹ * a * j = a := by
      calc j⁻¹ * a * j = j⁻¹ * (j * a * j⁻¹) * j := by rw [hja]
        _ = a := by group
    calc j⁻¹ * (t * ε * a) * j = (j⁻¹ * t * j) * (j⁻¹ * ε * j) * (j⁻¹ * a * j) := by group
      _ = t * (ε * b) * a := by rw [ht, hε, ha]
  have e3 : q * (t * (ε * b) * a) * q⁻¹ = t * b := by
    calc q * (t * (ε * b) * a) * q⁻¹
        = (q * t * q⁻¹) * (q * ε * q⁻¹) * (q * b * q⁻¹) * (q * a * q⁻¹) := by group
      _ = t * (ε * ε) * (a * b * a) := by
        rw [hqt, hqε, hqb, hqa]; group
      _ = t * b := by
        have : a * b * a = b := by
          calc a * b * a = b * a * a := by rw [hab]
            _ = b := by rw [mul_assoc, haa, mul_one]
        rw [hεε, this]; group
  calc (j * q * j⁻¹ * q⁻¹) * t * (j * q * j⁻¹ * q⁻¹)⁻¹
      = j * (q * (j⁻¹ * (q⁻¹ * t * q) * j) * q⁻¹) * j⁻¹ := by group
    _ = j * (t * b) * j⁻¹ := by rw [e1, e2, e3]
    _ = (j * t * j⁻¹) * (j * b * j⁻¹) := by group
    _ = t * b := by rw [hjt, hjb]

theorem comm_mem_centralizer_of_central_action {G : Type*} [Group G] {K E : Subgroup G} {z : G}
    (hKE : ∀ g ∈ K, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hKz : ∀ g ∈ K, g * z = z * g)
    (hact : ∀ g ∈ K, ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ zpowers z) {g g' : G} (hg : g ∈ K)
    (hg' : g' ∈ K) {e : G} (he : e ∈ E) :
    (g * g' * g⁻¹ * g'⁻¹) * e = e * (g * g' * g⁻¹ * g'⁻¹) := by
  have hZc : ∀ g ∈ K, ∀ w ∈ zpowers z, g * w = w * g := by
    rintro g hg w ⟨n, rfl⟩
    exact ((Commute.zpow_right (show Commute g z from hKz g hg) n).eq)
  have hZZ : ∀ w ∈ zpowers z, ∀ w' ∈ zpowers z, w * w' = w' * w := by
    rintro w ⟨n, rfl⟩ w' ⟨m, rfl⟩
    exact (Commute.zpow_zpow_self z n m).eq
  have hA : ∀ e ∈ E, (g * g') * e * (g * g')⁻¹ = (g' * g) * e * (g' * g)⁻¹ := by
    intro e he
    have hv := hact g hg e he
    have hw := hact g' hg' e he
    have h1 : (g * g') * e * (g * g')⁻¹ =
        (g' * e * g'⁻¹ * e⁻¹) * (g * e * g⁻¹ * e⁻¹) * e := by
      calc (g * g') * e * (g * g')⁻¹ = g * (g' * e * g'⁻¹) * g⁻¹ := by group
        _ = g * ((g' * e * g'⁻¹ * e⁻¹) * e) * g⁻¹ := by group
        _ = (g * (g' * e * g'⁻¹ * e⁻¹) * g⁻¹) * (g * e * g⁻¹ * e⁻¹) * e := by group
        _ = (g' * e * g'⁻¹ * e⁻¹) * (g * e * g⁻¹ * e⁻¹) * e := by
          rw [hZc g hg _ hw]; group
    have h2 : (g' * g) * e * (g' * g)⁻¹ =
        (g * e * g⁻¹ * e⁻¹) * (g' * e * g'⁻¹ * e⁻¹) * e := by
      calc (g' * g) * e * (g' * g)⁻¹ = g' * (g * e * g⁻¹) * g'⁻¹ := by group
        _ = g' * ((g * e * g⁻¹ * e⁻¹) * e) * g'⁻¹ := by group
        _ = (g' * (g * e * g⁻¹ * e⁻¹) * g'⁻¹) * (g' * e * g'⁻¹ * e⁻¹) * e := by group
        _ = (g * e * g⁻¹ * e⁻¹) * (g' * e * g'⁻¹ * e⁻¹) * e := by
          rw [hZc g' hg' _ hv]; group
    rw [h1, h2, hZZ _ hw _ hv]
  have hinv : (g' * g)⁻¹ ∈ K := inv_mem (mul_mem hg' hg)
  have he' : (g' * g)⁻¹ * e * ((g' * g)⁻¹)⁻¹ ∈ E := hKE _ hinv e he
  have key := hA _ he'
  have e1 : (g' * g) * ((g' * g)⁻¹ * e * ((g' * g)⁻¹)⁻¹) * (g' * g)⁻¹ = e := by group
  rw [e1] at key
  have key2 : (g * g' * g⁻¹ * g'⁻¹) * e * (g * g' * g⁻¹ * g'⁻¹)⁻¹ = e := by
    calc (g * g' * g⁻¹ * g'⁻¹) * e * (g * g' * g⁻¹ * g'⁻¹)⁻¹
        = (g * g') * ((g' * g)⁻¹ * e * ((g' * g)⁻¹)⁻¹) * (g * g')⁻¹ := by group
      _ = e := key
  calc (g * g' * g⁻¹ * g'⁻¹) * e = (g * g' * g⁻¹ * g'⁻¹) * e * (g * g' * g⁻¹ * g'⁻¹)⁻¹ *
        (g * g' * g⁻¹ * g'⁻¹) := by group
    _ = e * (g * g' * g⁻¹ * g'⁻¹) := by rw [key2]

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] def s56Eps (d : Data G) (m : G) : G := d.t * (m * d.t * m⁻¹)

theorem Hyp.s56_conj_t (hd : d.Hyp) (m : G) : m * d.t * m⁻¹ = d.t * d.s56Eps m := by
  rw [s56Eps, ← mul_assoc, hd.t_mul_self, one_mul]

theorem Hyp.s56_eps_mem_E (hd : d.Hyp) {m : G} (hm : m ∈ d.M) : d.s56Eps m ∈ d.E := by
  have hs : d.t * d.t ∈ d.E := by rw [hd.t_mul_self]; exact one_mem _
  exact (hd.thm52 hm hs).1

theorem Hyp.s56_eps_mul (hd : d.Hyp) (m m' : G) :
    d.s56Eps (m * m') = d.s56Eps m * (m * d.s56Eps m' * m⁻¹) := by
  have h1 := hd.s56_conj_t m'
  have h2 := hd.s56_conj_t m
  have ht := hd.t_mul_self
  have e : m * m' * d.t * (m * m')⁻¹ = (d.t * d.s56Eps m) * (m * d.s56Eps m' * m⁻¹) := by
    calc m * m' * d.t * (m * m')⁻¹ = m * (m' * d.t * m'⁻¹) * m⁻¹ := by group
      _ = m * (d.t * d.s56Eps m') * m⁻¹ := by rw [h1]
      _ = (m * d.t * m⁻¹) * (m * d.s56Eps m' * m⁻¹) := by group
      _ = (d.t * d.s56Eps m) * (m * d.s56Eps m' * m⁻¹) := by rw [h2]
  show d.t * (m * m' * d.t * (m * m')⁻¹) = _
  rw [e]
  calc d.t * (d.t * d.s56Eps m * (m * d.s56Eps m' * m⁻¹))
      = (d.t * d.t) * d.s56Eps m * (m * d.s56Eps m' * m⁻¹) := by group
    _ = _ := by rw [ht, one_mul]

theorem Hyp.s56_mem_Q0_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G} :
    m ∈ d.s56Q0 ↔ m ∈ d.M ∧ ∀ e ∈ d.E, m * e * m⁻¹ * e⁻¹ ∈ zpowers d.z := by
  have h := (hd.s56_structure_M h49).2.2.2.1
  have := Set.ext_iff.1 h m
  simpa using this

theorem Hyp.s56_Q0_le_M (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Q0 ≤ d.M :=
  fun _ hm => ((hd.s56_mem_Q0_iff h49).1 hm).1

theorem Hyp.s56_Q0_comm_mem_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) {m m' : G}
    (hm : m ∈ d.s56Q0) (hm' : m' ∈ d.s56Q0) : m * m' * m⁻¹ * m'⁻¹ ∈ d.s56Q2 := by
  obtain ⟨hmM, hmE⟩ := (hd.s56_mem_Q0_iff h49).1 hm
  obtain ⟨hm'M, hm'E⟩ := (hd.s56_mem_Q0_iff h49).1 hm'
  refine (Data.s56_mem_Q2_iff).2 ⟨mul_mem (mul_mem (mul_mem hmM hm'M) (inv_mem hmM)) (inv_mem hm'M),
    fun e he => ?_⟩
  exact (S56.comm_mem_centralizer_of_central_action (K := d.s56Q0) (E := d.E) (z := d.z)
    (fun g hg e he => (mem_normalizer_iff.1 (hd.s56_ME ((hd.s56_Q0_le_M h49) hg)) e).1 he)
    (fun g hg => hd.s56_M_comm_z ((hd.s56_Q0_le_M h49) hg))
    (fun g hg e he => ((hd.s56_mem_Q0_iff h49).1 hg).2 e he) hm hm' he).symm

theorem Hyp.s56_z_sq (hd : d.Hyp) : d.z * d.z = 1 := by
  have := hd.A_facts.2.2.1.2 d.z (s56_E_le_A d hd.s56_z_mem_E)
  simpa [pow_two] using this

theorem Hyp.s56_E_sq (hd : d.Hyp) {e : G} (he : e ∈ d.E) : e * e = 1 := by
  have := hd.A_facts.2.2.1.2 e (s56_E_le_A d he)
  simpa [pow_two] using this

theorem Hyp.s56_E_comm (hd : d.Hyp) {a b : G} (ha : a ∈ d.E) (hb : b ∈ d.E) : a * b = b * a :=
  congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨a, s56_E_le_A d ha⟩
    ⟨b, s56_E_le_A d hb⟩)

theorem Hyp.s56_zpowers_sq (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.z) : w * w = 1 := by
  obtain ⟨n, rfl⟩ := hw
  have hz2 := hd.s56_z_sq
  have hc : Commute d.z d.z := Commute.refl _
  rw [← zpow_add, ← two_mul, zpow_mul]
  have : d.z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  rw [this, one_zpow]

theorem Hyp.s56_zpowers_le_E (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.z) : w ∈ d.E :=
  (zpowers_le.2 hd.s56_z_mem_E) hw

theorem Hyp.s56_M_comm_zpowers (hd : d.Hyp) {g : G} (hg : g ∈ d.M) {w : G}
    (hw : w ∈ zpowers d.z) : g * w = w * g := by
  obtain ⟨n, rfl⟩ := hw
  exact (Commute.zpow_right (show Commute g d.z from hd.s56_M_comm_z hg) n).eq

theorem Hyp.s56_zpowers_comm (hd : d.Hyp) {w w' : G} (hw : w ∈ zpowers d.z)
    (hw' : w' ∈ zpowers d.z) : w * w' = w' * w :=
  hd.s56_E_comm (hd.s56_zpowers_le_E hw) (hd.s56_zpowers_le_E hw')

theorem Hyp.s56_comm_t (h49 : d.Thm49Statement) (hd : d.Hyp) {j q : G} (hj : j ∈ d.s56Q0)
    (hjt : j * d.t = d.t * j) (hq : q ∈ d.s56Q0) :
    (j * q * j⁻¹ * q⁻¹) * d.t * (j * q * j⁻¹ * q⁻¹)⁻¹ =
      d.t * (j * d.s56Eps q * j⁻¹ * (d.s56Eps q)⁻¹) ∧
    j * d.s56Eps q * j⁻¹ * (d.s56Eps q)⁻¹ ∈ zpowers d.z := by
  have hjM := hd.s56_Q0_le_M h49 hj
  have hqM := hd.s56_Q0_le_M h49 hq
  have hεE := hd.s56_eps_mem_E hqM
  have hεε := hd.s56_E_sq hεE
  have ha := ((hd.s56_mem_Q0_iff h49).1 hq).2 _ hεE
  have hb := ((hd.s56_mem_Q0_iff h49).1 hj).2 _ hεE
  refine ⟨?_, hb⟩
  set ε := d.s56Eps q with hε
  set a := q * ε * q⁻¹ * ε⁻¹ with hadef
  set b := j * ε * j⁻¹ * ε⁻¹ with hbdef
  have hεa : ε * a = a * ε := (hd.s56_E_comm hεE (hd.s56_zpowers_le_E ha))
  have hεb : ε * b = b * ε := (hd.s56_E_comm hεE (hd.s56_zpowers_le_E hb))
  have hjε : j * ε * j⁻¹ = ε * b := by
    rw [hεb]; rw [hbdef]; group
  have hqε : q * ε * q⁻¹ = ε * a := by
    rw [hεa]; rw [hadef]; group
  have hqt : q * d.t * q⁻¹ = d.t * ε := hd.s56_conj_t q
  have hjt' : j * d.t * j⁻¹ = d.t := by
    rw [hjt]; group
  have hcz : ∀ g ∈ d.M, ∀ w ∈ zpowers d.z, g * w * g⁻¹ = w := fun g hg w hw => by
    rw [hd.s56_M_comm_zpowers hg hw]; group
  exact S56.comm_conj_t (hd.s56_zpowers_comm ha hb) hεε (hd.s56_zpowers_sq ha)
    (hd.s56_zpowers_sq hb) hjt' hjε (hcz j hjM a ha) (hcz j hjM b hb) hqt hqε
    (hcz q hqM a ha) (hcz q hqM b hb)

theorem Hyp.s56_eps_one (hd : d.Hyp) : d.s56Eps 1 = 1 := by
  rw [s56Eps]; simp [hd.t_mul_self]

theorem Hyp.s56_eps_conj (hd : d.Hyp) {g : G} (hg : g * d.t = d.t * g) (m : G) :
    d.s56Eps (g * m * g⁻¹) = g * d.s56Eps m * g⁻¹ := by
  have hgt : g * d.t * g⁻¹ = d.t := by rw [hg]; group
  calc d.s56Eps (g * m * g⁻¹) = (g * d.t * g⁻¹) * (g * m * g⁻¹ * (g * d.t * g⁻¹) *
        (g * m * g⁻¹)⁻¹) := by rw [s56Eps, hgt]
    _ = g * (d.t * (m * d.t * m⁻¹)) * g⁻¹ := by group
    _ = g * d.s56Eps m * g⁻¹ := rfl

theorem Hyp.s56_eps_mul_Q2 (hd : d.Hyp) {q m : G} (hq : q ∈ d.s56Q2) (hm : m ∈ d.M) :
    d.s56Eps (q * m) = d.s56Eps q * d.s56Eps m := by
  rw [hd.s56_eps_mul]
  congr 1
  have hεE := hd.s56_eps_mem_E hm
  have := ((s56_mem_Q2_iff).1 hq).2 _ hεE
  calc q * d.s56Eps m * q⁻¹ = d.s56Eps m * q * q⁻¹ := by rw [this]
    _ = d.s56Eps m := by group

theorem Hyp.s56_eps_inv_Q2 (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q2) :
    d.s56Eps q⁻¹ = d.s56Eps q := by
  have hqM : q ∈ d.M := ((s56_mem_Q2_iff).1 hq).1
  have h1 := hd.s56_eps_mul_Q2 hq (inv_mem hqM)
  rw [mul_inv_cancel, hd.s56_eps_one] at h1
  have hεE := hd.s56_eps_mem_E hqM
  have h2 : d.s56Eps q * d.s56Eps q = 1 := hd.s56_E_sq hεE
  have h3 : d.s56Eps q⁻¹ = (d.s56Eps q)⁻¹ := (inv_eq_of_mul_eq_one_right h1.symm).symm
  rw [h3]
  exact (inv_eq_of_mul_eq_one_right h2)

theorem Hyp.s56_eps_mul_Q2' (hd : d.Hyp) {q q' : G} (hq : q ∈ d.s56Q2) (hq' : q' ∈ d.s56Q2) :
    d.s56Eps (q * q') = d.s56Eps q * d.s56Eps q' :=
  hd.s56_eps_mul_Q2 hq ((s56_mem_Q2_iff).1 hq').1

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
